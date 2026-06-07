const express = require("express");
const cors = require("cors");
const rateLimit = require("express-rate-limit");
const path = require("path");

const app = express();
const PORT = process.env.PORT || 3000;
const API_KEY = process.env.PAE_API_KEY;

// WASM engine state
let paeModule = null;
let paeEngine = 0;

async function initWasm() {
  const PolyModule = require("./wasm/poly_wasm.js");
  paeModule = await PolyModule({
    locateFile: (file) => path.join(__dirname, "wasm", file),
  });
  paeEngine = paeModule._poly_create_engine();
  console.log("PAE WASM engine ready");
}

function callPae(fn, expression) {
  const ptr = paeModule.ccall(fn, "number", ["number", "string"], [paeEngine, expression]);
  const result = paeModule.UTF8ToString(ptr);
  paeModule._poly_free_string(ptr);
  return result;
}

function callPaeWithVar(fn, expression, variable) {
  const varChar = variable.charCodeAt(0);
  const ptr = paeModule.ccall(fn, "number", ["number", "string", "number"], [paeEngine, expression, varChar]);
  const result = paeModule.UTF8ToString(ptr);
  paeModule._poly_free_string(ptr);
  return result;
}

// Middleware
app.use(cors());
app.use(express.json());

app.use(rateLimit({
  windowMs: 60 * 1000,
  max: 120,
  message: { error: "Too many requests" },
}));

function authMiddleware(req, res, next) {
  if (!API_KEY) return next();
  const key = req.headers["x-api-key"];
  if (key !== API_KEY) return res.status(401).json({ error: "Unauthorized" });
  next();
}

// Health check (no auth)
app.get("/", (req, res) => res.json({ status: "ok", service: "PAE Bird API" }));

// Math endpoints
app.post("/solve", authMiddleware, (req, res) => {
  const { expression } = req.body;
  if (!expression) return res.status(400).json({ error: "expression required" });
  try {
    res.json({ result: callPae("poly_solve_equation", expression) });
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

app.post("/expand", authMiddleware, (req, res) => {
  const { expression } = req.body;
  if (!expression) return res.status(400).json({ error: "expression required" });
  try {
    res.json({ result: callPae("poly_expand", expression) });
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

app.post("/factor", authMiddleware, (req, res) => {
  const { expression } = req.body;
  if (!expression) return res.status(400).json({ error: "expression required" });
  try {
    res.json({ result: callPae("poly_factor_polynomial", expression) });
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

app.post("/differentiate", authMiddleware, (req, res) => {
  const { expression, variable = "x" } = req.body;
  if (!expression) return res.status(400).json({ error: "expression required" });
  try {
    res.json({ result: callPaeWithVar("poly_differentiate", expression, variable) });
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

app.post("/integrate", authMiddleware, (req, res) => {
  const { expression, variable = "x" } = req.body;
  if (!expression) return res.status(400).json({ error: "expression required" });
  try {
    res.json({ result: callPaeWithVar("poly_integrate", expression, variable) });
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

initWasm().then(() => {
  app.listen(PORT, () => console.log(`PAE API listening on port ${PORT}`));
}).catch((e) => {
  console.error("Failed to init WASM:", e);
  process.exit(1);
});
