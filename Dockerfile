FROM debian:bookworm-slim

# chezscheme: the Chez Scheme engine itself (verified working via
# `apt-get install chezscheme` on debian:bookworm-slim/amd64 -- Railway's
# actual runtime architecture -- with no explicit boot-file path needed;
# the packaged `scheme` binary already has its own default baked in).
# nodejs/npm: this is still a Node/Express server; Chez is invoked as a
# subprocess per request (computeViaChez() in index.js), not a rewrite.
RUN apt-get update && apt-get install -y --no-install-recommends \
    chezscheme nodejs npm ca-certificates \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app
COPY package*.json ./
RUN npm ci --omit=dev
COPY . .

ENV PORT=3000
EXPOSE 3000
CMD ["node", "index.js"]
