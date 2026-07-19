const express = require("express");
const cors = require("cors");
const rateLimit = require("express-rate-limit");
const path = require("path");
const { execFile } = require("child_process");

const app = express();
app.set("trust proxy", 1);
const PORT = process.env.PORT || 3000;
const API_KEY = process.env.PAE_API_KEY;
const FREE_KEY = process.env.PAE_FREE_KEY;
const PAID_KEY = process.env.PAE_PAID_KEY;
const FRIEND_KEY = process.env.PAE_FRIEND_KEY;
const FRIEND_KEY_LIMIT = 10;

// Chez Scheme engine invocation. Reuses chez-engine/dispatcher.scm's
// "compute" mode directly (added to math-edu-scheme's chez/dispatcher.scm
// specifically for this API) -- one subprocess per request, exactly
// mirroring the same subprocess-bridge pattern already used elsewhere in
// this project (PolyProcessor.mm's NSTask bridge, xlsxtool's bridge),
// rather than reimplementing the engine's dispatch logic here. This
// replaces the old WASM/C++ engine entirely: besides two demonstrated
// solve() bugs in that engine's history, it has no matrix or factorial
// support at all (those are Chez/MIT-only features), so it could never
// reach feature parity with the app regardless of how "fixed" it is.
//
// CHEZ_BIN/CHEZ_BOOT let this run against a local macOS Chez build in
// dev (see README) and a Linux one (installed via apt in the Dockerfile)
// in production, without code changes.
const CHEZ_BIN = process.env.CHEZ_BIN || "scheme";
const CHEZ_BOOT = process.env.CHEZ_BOOT || null;
const ENGINE_DIR = path.join(__dirname, "chez-engine");

function computeViaChez(cmd, arg, expression) {
  return new Promise((resolve, reject) => {
    const args = CHEZ_BOOT ? ["-q", "-b", CHEZ_BOOT] : ["-q"];
    args.push("--script", "dispatcher.scm", "compute", cmd, arg == null ? "" : arg, expression);
    execFile(CHEZ_BIN, args, { cwd: ENGINE_DIR, timeout: 10000 }, (err, stdout, stderr) => {
      if (err) return reject(new Error(stderr ? stderr.trim() : err.message));
      resolve(stdout.replace(/\n$/, ""));
    });
  });
}

// Usage tracking -- generalized to any command name, not a fixed list,
// since this API now covers every chez/dispatcher.scm operation.
const startTime = Date.now();
const counts = {};
function trackUsage(cmd) {
  counts[cmd] = (counts[cmd] || 0) + 1;
}

// Middleware
app.use(cors());
app.use(express.json());

app.use(rateLimit({
  windowMs: 60 * 1000,
  max: 120,
  message: { error: "Too many requests" },
}));

const freeTierLimiter = rateLimit({
  windowMs: 24 * 60 * 60 * 1000,
  max: 50,
  keyGenerator: (req) => req.ip,
  message: { error: "Free tier daily limit reached. Upgrade at https://paebird.com/register.html" },
});

// Friend/trial key -- a total-use cap (not a time-windowed rate limit like
// the other tiers), for handing out a single short-lived key to a handful
// of people to try the paid experience without going through PayPal.
// In-memory like freeTierLimiter's own counters, so a redeploy resets it --
// fine for a small trial cap, not meant to be durable.
let friendKeyUses = 0;
function friendKeyLimiter(req, res, next) {
  if (friendKeyUses >= FRIEND_KEY_LIMIT) {
    return res.status(429).json({ error: `This trial key has reached its ${FRIEND_KEY_LIMIT}-use limit.` });
  }
  friendKeyUses++;
  next();
}

// Paid subscribers (PayPal-issued, see register.html) get no daily cap --
// only the global 120/min flood-protection limiter above still applies.
// Deliberately a separate value from API_KEY (the developer's own
// unrestricted testing credential): rotating one if it ever leaks
// shouldn't force rotating the other.
function authMiddleware(req, res, next) {
  if (!API_KEY) return next();
  const key = req.headers["x-api-key"];
  if (key === API_KEY) return next();
  if (PAID_KEY && key === PAID_KEY) return next();
  if (FRIEND_KEY && key === FRIEND_KEY) return friendKeyLimiter(req, res, next);
  if (FREE_KEY && key === FREE_KEY) return freeTierLimiter(req, res, next);
  return res.status(401).json({ error: "Unauthorized" });
}

// Health check (no auth)
app.get("/", (req, res) => res.json({ status: "ok", service: "PAE Bird API", engine: "chez" }));

// Usage stats (auth required)
app.get("/stats", authMiddleware, (req, res) => {
  const uptimeHours = ((Date.now() - startTime) / 3600000).toFixed(2);
  const total = Object.values(counts).reduce((a, b) => a + b, 0);
  res.json({ uptime_hours: Number(uptimeHours), requests: counts, total });
});

// Shared handler for a fixed-cmd route (the 5 pre-existing endpoints,
// kept for backward compatibility with the already-deployed Sheets/
// LibreOffice clients -- same request/response shape as before, just
// backed by the Chez engine internally now).
function fixedCmdRoute(cmd) {
  return async (req, res) => {
    const { expression, variable = "" } = req.body;
    if (!expression) return res.status(400).json({ error: "expression required" });
    try {
      trackUsage(cmd);
      res.json({ result: await computeViaChez(cmd, variable, expression) });
    } catch (e) {
      res.status(500).json({ error: e.message });
    }
  };
}

app.post("/solve", authMiddleware, fixedCmdRoute("solve"));
app.post("/expand", authMiddleware, fixedCmdRoute("expand"));
app.post("/factor", authMiddleware, fixedCmdRoute("factor"));
app.post("/differentiate", authMiddleware, fixedCmdRoute("differentiate"));
app.post("/integrate", authMiddleware, fixedCmdRoute("integrate"));

// Generic endpoint covering every other chez/dispatcher.scm operation
// (solveexp, solvelog, radical, rational, trig, conic, domain, range,
// compose, inverse, system, inequality, expandc, logtoexp, exptolog,
// rotate, flip, degtorad, radtodeg, sqrt, sci, balance, oxstate, canon),
// plus matrix operations and factorial -- both of which work implicitly
// through any cmd (matching the engine's own transparent design), so
// e.g. {cmd:"expand", expression:"det([[1,2],[3,4]])"} or
// {cmd:"expand", expression:"5!"} both work with no special-casing here.
// Mirrors dispatcher.scm's own cmd/arg/expression parameters exactly --
// adding a new engine operation later needs no new server code at all.
app.post("/compute", authMiddleware, async (req, res) => {
  const { cmd = "expand", arg = "", expression } = req.body;
  if (!expression) return res.status(400).json({ error: "expression required" });
  if (typeof cmd !== "string" || cmd.length === 0) {
    return res.status(400).json({ error: "cmd must be a non-empty string" });
  }
  try {
    trackUsage(cmd);
    res.json({ result: await computeViaChez(cmd, arg, expression) });
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

app.listen(PORT, () => console.log(`PAE API listening on port ${PORT} (Chez engine)`));
