# Procedural Canvas DSL

A tiny Lisp-like language, written in [Racket](https://racket-lang.org/) with
`web-server`, that turns code into **SVG art** in the browser. It also converts
an uploaded image (JPG/PNG) into editable DSL code.

**Live:** https://racket.micutu.com

The whole app is a single file (`app.rkt`): a hardened S-expression parser, a
bounded interpreter, and a server-rendered, mobile-first UI.

---

## Language reference

A program is a sequence of commands. Numbers can be arithmetic expressions;
colors can be literals or computed builders. Inside `(repeat N ...)` the
variable `i` is the current iteration index.

### Shapes
| Command | Meaning |
| --- | --- |
| `(circle x y r color)` | circle |
| `(rect x y w h color)` | rectangle |
| `(ellipse cx cy rx ry color)` | ellipse |
| `(line x1 y1 x2 y2 color width)` | line |
| `(polygon color x1 y1 x2 y2 ...)` | filled polygon |
| `(polyline color width x1 y1 ...)` | open stroked path |
| `(star cx cy spikes r-outer r-inner color)` | star / n-gon burst |
| `(text x y size color "string")` | text |
| `(bg color)` | fill the whole 600×400 canvas |

### Control & variables
| Command | Meaning |
| --- | --- |
| `(repeat N cmd ...)` | run the body `N` times; `i` = index |
| `(let ([name expr] ...) cmd ...)` | bind computed locals |

### Numbers
`+  -  *  /  mod  pow  sin  cos  tan  sqrt  abs  neg  floor  round  min  max`
plus `(random max)`, `(random lo hi)`, and the constants `pi  tau  width  height`.

### Colors
`"#rrggbb"` · CSS names (`"red"`, `"tomato"`) · `(rgb r g b)` · `(rgba r g b a)`
· `(hsl h s l)` · `(hsla h s l a)`. Channels are clamped to valid ranges.

### Example

```racket
(bg "#0b0f1a")
(repeat 90
  (circle (+ 300 (* (* i 2.2) (cos (* i 0.35))))
          (+ 200 (* (* i 2.2) (sin (* i 0.35))))
          6
          (hsl (* i 5) 85 60)))
(star 300 200 5 40 16 "#f1fa8c")
```

---

## Security model

The endpoint is public and unauthenticated, so **every input is treated as
hostile**. Defenses live in `app.rkt`:

- **Bounded evaluation** — a shared element budget (`MAX-ELEMENTS`) plus caps on
  `repeat` count, nesting depth, number magnitude, and expression depth. A
  payload like `(repeat 99999999 ...)` or nested `repeat`s returns in
  milliseconds, truncated, instead of exhausting CPU/RAM.
- **Hardened reader** — `read-accept-graph` is off (blocks cyclic `#0=(1 . #0#)`
  payloads that caused infinite traversal), and `read-accept-reader` /
  `read-accept-compiled` are off (no code loading at read time).
- **Clamped output** — numbers go through `fmt-num` (no invalid `1/3`, no huge
  bignums); colors are validated/whitelisted on top of xexpr's escaping.
- **Input limits** — DSL length, upload size, image resolution, point counts,
  spike counts and text length are all capped.
- **Robust I/O** — malformed / non-UTF-8 request bodies degrade to empty
  bindings instead of a 500.

Infrastructure (see the config files) adds:
- **systemd sandbox** with `MemoryMax` / `CPUQuota` / `TasksMax` — a runaway
  render is confined, not fatal to the host.
- **nginx**: Cloudflare-origin lockdown, per-IP rate limit, `client_max_body_size`,
  and an explicit CSP (also allowing the injected Umami script).

---

## Running locally

```bash
raco make app.rkt          # optional: compile
RACKET_APP_PORT=8346 racket app.rkt
# open http://127.0.0.1:8346/
```

`GET /health` returns `ok` for uptime checks.

---

## Deployment (this VPS)

The service runs on `127.0.0.1:8345` behind nginx + Cloudflare.

1. **App** — the systemd unit runs `app.rkt` directly, so deploying app changes
   is just a restart:
   ```bash
   sudo cp racket-app.service /etc/systemd/system/racket-app.service
   sudo systemctl daemon-reload
   sudo systemctl restart racket-app
   systemctl status racket-app --no-pager
   curl -s http://127.0.0.1:8345/health   # -> ok
   ```
2. **nginx**:
   ```bash
   sudo cp racket-rate-limit.conf /etc/nginx/conf.d/racket-rate-limit.conf
   sudo cp racket.micutu.com.conf /etc/nginx/sites-available/racket.micutu.com.conf
   sudo nginx -t && sudo systemctl reload nginx
   ```

---

## Files

| File | Purpose |
| --- | --- |
| `app.rkt` | the entire application (parser, interpreter, UI) |
| `racket-app.service` | hardened systemd unit |
| `racket.micutu.com.conf` | hardened nginx vhost |
| `racket-rate-limit.conf` | nginx rate-limit zone (http context) |
