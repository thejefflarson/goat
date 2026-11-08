# Builds the browser editor into a static site served by unprivileged nginx.
# Context is the repository root: docker build -f web/Dockerfile .
# Stages are not pinned to $BUILDPLATFORM: each arch builds on its own native
# BuildKit node, so a cross-arch stage would fall back to QEMU.

FROM rust:1-slim-bookworm@sha256:f2c004e3d2d8b547e8cf7ffbc29205385f4e71d23e53e4e383065db5e9f822cd AS compiler
WORKDIR /src
RUN rustup target add wasm32-unknown-unknown
COPY . .
RUN --mount=type=cache,target=/usr/local/cargo/git/db \
    --mount=type=cache,target=/usr/local/cargo/registry \
    cargo build --locked -p goat_web --target wasm32-unknown-unknown --release

FROM node:24-alpine@sha256:a34ab6d7f6f4813f4d0c5469d74685604b962fbdbf5793a7bc7b4998ecb867c8 AS site
WORKDIR /src/web
COPY web/package.json web/package-lock.json ./
RUN npm ci --ignore-scripts
COPY web/ ./
COPY --from=compiler /src/target/wasm32-unknown-unknown/release/goat_web.wasm ../target/wasm32-unknown-unknown/release/goat_web.wasm
RUN npm run build && npm run bundle

# Runs as the image's built-in uid 101 on 8080; nginx writes only under /tmp.
FROM nginxinc/nginx-unprivileged:1-alpine@sha256:b5047b9b76845eac124358373c6852377c52e4b05834a47647e955dd91cb8f1e
COPY web/nginx.conf /etc/nginx/conf.d/default.conf
COPY --from=site /src/web/site /srv/site
HEALTHCHECK NONE
EXPOSE 8080
