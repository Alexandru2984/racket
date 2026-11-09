# Procedural Canvas DSL

A tiny Lisp-like language, written in [Racket](https://racket-lang.org/) with
`web-server`, that turns code into **generative SVG art** in the browser. Write
loops, trigonometry, noise, gradients and animation; render it live, then
download it as **SVG or PNG** or share it with a **permalink**. It also converts
an uploaded image (JPG/PNG) into editable DSL code.

**Live:** https://racket.micutu.com

The whole app is a single file (`app.rkt`): a hardened S-expression parser, a
resource-bounded interpreter, a server-rendered mobile-first UI, and a small
JSON/SVG API for the live editor.

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
| `(ring cx cy r color width)` | stroked circle (no fill) |
| `(arc cx cy r a0 a1 color width)` | stroked circular arc (degrees) |
| `(triangle x1 y1 x2 y2 x3 y3 color)` | filled triangle |
| `(poly cx cy sides r color)` | filled regular n-gon |
| `(heart cx cy size color)` | filled heart |
| `(sector cx cy r a0 a1 color)` | filled pie slice (degrees) |
| `(spiral cx cy turns r0 r1 color width)` | Archimedean spiral |
| `(curve color width x1 y1 x2 y2 ...)` | smooth open curve through points |
| `(polygon color x1 y1 x2 y2 ...)` | filled polygon |
| `(polyline color width x1 y1 ...)` | open stroked path |
| `(star cx cy spikes r-outer r-inner color)` | star / n-gon burst |
| `(text x y size color "string")` | text |
| `(bg color)` | fill the whole 600×400 canvas |

### Control & variables
| Command | Meaning |
| --- | --- |
| `(repeat N cmd ...)` | run the body `N` times; `i` = index |
| `(for name start end [step] cmd ...)` | ranged loop binding `name` (step optional) |
| `(grid cols rows cmd ...)` | nested loop exposing `gx` (col), `gy` (row), `gi` (flat) |
| `(let ([name expr] ...) cmd ...)` | bind computed locals |
| `(seed N)` | seed `(random ...)` for reproducible art |

### Transforms & animation
Transforms and animations wrap a body of commands in an SVG `<g>`; animation is
SVG-native, so motion is preserved in the downloaded `.svg` (no JavaScript).

| Command | Meaning |
| --- | --- |
| `(group cmd ...)` | group commands |
| `(rotate deg cx cy cmd ...)` | rotate the body around `(cx, cy)` |
| `(translate dx dy cmd ...)` | translate the body |
| `(scale sx sy cmd ...)` | scale the body |
| `(opacity a cmd ...)` | apply group opacity `a` in `[0,1]` |
| `(spin cx cy seconds cmd ...)` | continuously rotate the body |
| `(pulse seconds cmd ...)` | continuously fade the body in/out |
| `(blur px cmd ...)` | gaussian blur the body |
| `(glow color cmd ...)` | colored outer glow |
| `(shadow dx dy px color cmd ...)` | drop shadow |
| `(stroke color width cmd ...)` | outline the shapes in the body |
| `(dash on off cmd ...)` | make their strokes dashed |

Effects are SVG `<filter>`s registered in `<defs>` (preserved in downloads, no
JavaScript); identical filters are deduplicated per render.

### Numbers
`+  -  *  /  mod  pow  sin  cos  tan  atan  atan2  sqrt  exp  log  abs  neg
sign  floor  round  ceil  min  max  hypot` plus:

| Expression | Meaning |
| --- | --- |
| `(dist x1 y1 x2 y2)` | Euclidean distance |
| `(lerp a b t)` | linear interpolation |
| `(clamp x lo hi)` | clamp to a range |
| `(map v in-lo in-hi out-lo out-hi)` | remap between ranges |
| `(noise x y)` / `(noise x y z)` | smooth value noise in `[0,1]` |
| `(random max)` / `(random lo hi)` | bounded random integers |

Constants: `pi  tau  width  height`.

### Colors
`"#rrggbb"` · CSS names (`"red"`, `"tomato"`) · `(rgb r g b)` · `(rgba r g b a)`
· `(hsl h s l)` · `(hsla h s l a)`. Channels are clamped to valid ranges.

| Builder | Meaning |
| --- | --- |
| `(hsv h s v)` | HSV color (hue 0–360, sat/value 0–100) |
| `(palette "name" i)` | curated palette: fire, ocean, neon, pastel, sunset, forest, mono, ice, lava, candy, earth, aurora, retro |
| `(mix c1 c2 t)` | blend any two colors in RGB at `t` in `[0,1]` |
| `(linear angle c1 c2 ...)` | gradient **fill** for a shape (per-shape, any shape) |
| `(radial c1 c2 ...)` | radial gradient fill for a shape |
| `(linear-bg deg c1 c2 ...)` | fill the canvas with a linear gradient |
| `(radial-bg c1 c2 ...)` | fill the canvas with a radial gradient |

### Example — a noise flow field

```racket
(linear-bg 90 "#05070f" "#0f1630")
(seed 7)
(repeat 1400
  (let ([x (random 600)] [y (random 400)]
        [a (* 6.28 (noise (* x 0.012) (* y 0.012)))])
    (line x y (+ x (* 14 (cos a))) (+ y (* 14 (sin a)))
          (mix "#8be9fd" "#bd93f9" (noise (* x 0.02) (* y 0.02))) 1.5)))
```

---

## Features

- **Live preview** — the editor renders as you type (debounced); `Ctrl+Enter`
  renders now, `Tab` indents. A status line shows element count and render time.
- **Pro editor** — syntax highlighting, a line-number gutter, auto-closing
  parens/quotes, an inline error bar and command autocomplete (caret-anchored,
  keyboard-navigable), all as progressive enhancement over a plain textarea.
- **Export** — download the art as **SVG** (server) or **PNG** (client-side
  canvas rasterization at 2×).
- **Share** — the 🔗 button builds a `?c=<base64>` permalink of the current
  program and copies it to the clipboard.
- **Surprise** — five seeded generators (flow field, vortex, kaleidoscope,
  polar rose, pulsing rings) produce new art in one click.
- **Community gallery** — save a creation and browse everyone's work, with
  one-tap ♥ likes (one per IP), a recent/popular toggle, and a per-creation
  share page (`/g/<id>`) that carries its own Open Graph preview. Public and
  unauthenticated, so it is bounded on every axis (see below). Optional
  moderation: set `GALLERY_ADMIN_TOKEN` and visit `/gallery?admin=<token>` to
  delete entries; admin is fully off when the token is unset.
- **Image → DSL** — upload a JPG/PNG and get editable DSL circles back.
- **Light / dark theme** — 🌓 toggle, persisted in `localStorage` and applied
  before first paint (the editor and canvas stay dark by design).
- **No-JavaScript fallback** — every action is also a plain POST form or link,
  so the page works with scripting disabled.

---

## HTTP endpoints

| Route | Purpose |
| --- | --- |
| `GET /` | the editor + canvas page (accepts `?c=<base64>` permalinks) |
| `POST /` | `action=preview` (render), `action=download` (SVG file), `action=upload` (image → DSL) |
| `POST /api/render` | render `code` to SVG; `X-Render-Ms` / `X-Elements` headers |
| `POST /api/save` | save a creation (JSON), for the no-reload save button |
| `POST /api/like` | like a creation once per IP (JSON) |
| `POST /api/delete` | admin-only delete (requires `GALLERY_ADMIN_TOKEN`) |
| `GET /gallery?sort=popular` | gallery ordered by likes |
| `GET /g/<id>` | per-creation share page (own Open Graph preview) |
| `POST /` + `action=save` | save a creation to the gallery (303 → `/gallery`; no-JS fallback) |
| `GET /gallery` | the community gallery (paginated via `?before=<id>`) |
| `GET /thumb/<id>` | a saved creation's thumbnail, as an inert SVG image |
| `GET /app.js` | the front-end script (served same-origin for CSP) |
| `GET /og.png` | 1200×630 Open Graph image, rendered once with `racket/draw` |
| `GET /sitemap.xml` | sitemap for the public page |
| `GET /health` | returns `ok` for uptime checks |

---

## Security model

The endpoint is public and unauthenticated, so **every input is treated as
hostile**. The core defense is that **work is bounded regardless of whether a
shape is ever emitted** — an input that does millions of operations without
drawing anything can no longer bypass the caps.

- **Three internal budgets**, charged during interpretation:
  - *element budget* (`MAX-ELEMENTS`) — total emitted shapes;
  - *fuel* (`MAX-FUEL`) — every expression node, loop iteration and command
    burns a unit, so empty `let` bodies, giant arithmetic and invalid-command
    floods are bounded;
  - *point budget* (`MAX-TOTAL-POINTS`) — polygon/polyline/star vertices, which
    caps serialized output so point amplification can't balloon the response.
  - Error nodes also cost element budget and are capped, so a program of all
    invalid commands can't flood the output with error text.
- **Hard backstop** — each render runs under `call-with-limits` (a 3 s
  wall-clock + 96 MB ceiling in a child custodian), so even an unforeseen
  pathological path is killed and confined to that one request instead of
  OOM-ing the shared process.
- **Hardened reader** — `read-accept-graph` is off (blocks cyclic `#0=(1 . #0#)`
  payloads), and `read-accept-reader` / `read-accept-compiled` are off (no code
  loading at read time). Input length is capped before `read`.
- **Clamped output** — numbers go through `fmt-num` (no invalid `1/3`, no huge
  bignums; `pow` can't raise or allocate bignums); colors are validated on top
  of xexpr's escaping.
- **Isolated randomness** — each render runs under a fresh PRG, so `(seed N)` is
  reproducible and never leaks between requests.
- **Robust I/O** — malformed / non-UTF-8 request bodies degrade to empty
  bindings instead of a 500.
- **Gallery writes** (public, unauthenticated) are bounded too: a SQLite ring
  buffer caps the row count (so disk is bounded), with per-entry caps on title,
  code and stored SVG, a per-IP cooldown, and a minimum element count to reject
  blank/garbage saves. All SQL is parameterized; thumbnails are served as inert
  SVG images and titles are escaped, so a `<script>` title is stored and shown
  as literal text.

Infrastructure (see the config files) adds:
- **systemd sandbox** with `MemoryMax` / `CPUQuota` / `TasksMax` and a strict
  syscall filter — a runaway render is confined, not fatal to the host.
- **nginx**: Cloudflare-origin lockdown, per-IP rate limit, `client_max_body_size`,
  and an explicit CSP (`script-src 'self'` serves `/app.js`; also allows the
  injected Umami script).

---

## Tests & CI

The resource caps and DSL features have a `rackunit` regression suite in a
`(module+ test ...)` submodule — each previously-unbounded payload must return
well under the time limit with bounded node count and output size.

```bash
raco test app.rkt
```

GitHub Actions (`.github/workflows/ci.yml`) compiles the app, runs the suite,
boots the server to smoke-check every route (including the `racket/draw` OG
image), and validates the served `app.js` with Node.

---

## Running locally

```bash
raco make app.rkt          # optional: compile
RACKET_APP_PORT=8346 racket app.rkt
# open http://127.0.0.1:8346/
```

Running the file starts the server (the `main` submodule); requiring it does
not, so the interpreter can be tested in isolation.

---

## Deployment (this VPS)

The service runs on `127.0.0.1:8345` behind nginx + Cloudflare as the
`racket-canary` systemd unit, from `/srv/canary/racket.micutu.com/app`.

```bash
raco make app.rkt                       # refresh bytecode
sudo systemctl restart racket-canary
curl -s http://127.0.0.1:8345/health    # -> ok
```

nginx / rate-limit templates in this repo are deployed with:

```bash
sudo cp racket-rate-limit.conf /etc/nginx/conf.d/racket-rate-limit.conf
sudo cp racket.micutu.com.conf /etc/nginx/sites-available/racket.micutu.com.conf
sudo nginx -t && sudo systemctl reload nginx
```

---

## Files

| File | Purpose |
| --- | --- |
| `app.rkt` | the entire application (parser, interpreter, API, gallery, UI) |
| `gallery.sqlite` | runtime community-gallery store (gitignored) |
| `.github/workflows/ci.yml` | compile + test + smoke-check pipeline |
| `racket-app.service` | hardened systemd unit (template) |
| `racket.micutu.com.conf` | hardened nginx vhost (template) |
| `racket-rate-limit.conf` | nginx rate-limit zone (http context) |
