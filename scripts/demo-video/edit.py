#!/usr/bin/env python3
"""Assemble the recorded operator flow into a publishable MP4.

    python3 scripts/demo-video/edit.py [BUILD_DIR] [OUT.mp4]

Reads BUILD_DIR/timeline.json + frames/ written by record.ts. Each marker
starts a segment with a caption and a playback speed; segments with speed > 1
are time-compressed and carry a visible "N× time-lapse" badge. Nothing is
re-staged: every frame shown is a captured frame of the real UI.
"""
import bisect, json, os, subprocess, sys
from PIL import Image, ImageDraw, ImageFont, ImageFilter

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "../.."))
BUILD = sys.argv[1] if len(sys.argv) > 1 else os.path.join(REPO, ".video-build")
OUT = sys.argv[2] if len(sys.argv) > 2 else os.path.join(REPO, "docs/video/factory-workbench-demo.mp4")
W, H, FPS = 1920, 1080, 30
# Avenir Next ships with macOS; elsewhere set VIDEO_FONT to any .ttf/.ttc
# (weights then all use that one face) or Pillow's default font is used.
AV = os.environ.get("VIDEO_FONT", "/System/Library/Fonts/Avenir Next.ttc")
def F(size, idx):
    if not os.path.exists(AV):
        return ImageFont.load_default(size)
    try:
        return ImageFont.truetype(AV, size, index=idx if AV.endswith(".ttc") else 0)
    except OSError:
        return ImageFont.truetype(AV, size)
BOLD, DEMI, MED, REG = 0, 2, 5, 7
ACCENT = (245, 165, 36)
INK = (236, 238, 242)
MUTED = (160, 168, 182)

tl = json.load(open(os.path.join(BUILD, "timeline.json")))
frames = sorted(tl["frames"], key=lambda x: x["t"])
ft = [f["t"] for f in frames]
marks = tl["marks"]

# ---------------------------------------------------------------- timeline
segs = []  # (src_start, src_end, speed, caption, sub, scene)
for a, b in zip(marks, marks[1:]):
    if b["t"] > a["t"]:
        segs.append((a["t"], b["t"], a["speed"], a["caption"], a.get("sub", ""), a["scene"]))

def wrap(draw, text, font, width):
    words, lines, cur = text.split(), [], ""
    for w in words:
        t = (cur + " " + w).strip()
        if draw.textlength(t, font=font) <= width:
            cur = t
        else:
            lines.append(cur)
            cur = w
    if cur:
        lines.append(cur)
    return lines

def caption_layer(caption, sub, speed):
    im = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    d = ImageDraw.Draw(im)
    if caption:
        fc, fs = F(40, DEMI), F(27, MED)
        lines = wrap(d, caption, fc, 1500)
        sublines = wrap(d, sub, fs, 1500) if sub else []
        h = 44 + 52 * len(lines) + (12 + 36 * len(sublines) if sublines else 0)
        x0, y0 = 150, H - 60 - h
        box = Image.new("RGBA", (W - 300, h), (12, 14, 20, 222))
        im.alpha_composite(box, (x0, y0))
        d.rectangle([x0, y0, x0 + 7, y0 + h], fill=ACCENT + (255,))
        y = y0 + 22
        for ln in lines:
            d.text((x0 + 36, y), ln, font=fc, fill=INK)
            y += 52
        y += 12
        for ln in sublines:
            d.text((x0 + 36, y), ln, font=fs, fill=MUTED)
            y += 36
    if speed > 1:
        txt = f"{speed:g}×  TIME-LAPSE"
        fb = F(28, BOLD)
        tw = d.textlength(txt, font=fb)
        d.rounded_rectangle([W - 90 - tw - 40, 40, W - 90, 96], radius=14, fill=(12, 14, 20, 225), outline=ACCENT + (255,), width=3)
        d.text((W - 90 - tw - 20, 50), txt, font=fb, fill=ACCENT)
    tag = "Real system  ·  model output mocked"
    ft_ = F(22, MED)
    tw = d.textlength(tag, font=ft_)
    d.rounded_rectangle([W - 60 - tw - 28, H - 48, W - 60, H - 14], radius=10, fill=(12, 14, 20, 200))
    d.text((W - 60 - tw - 14, H - 45), tag, font=ft_, fill=MUTED)
    return im

def card(title, lines, kicker=None, foot=None):
    im = Image.new("RGB", (W, H), (13, 15, 21))
    d = ImageDraw.Draw(im)
    for i in range(H):  # subtle vertical gradient
        c = int(13 + 10 * i / H)
        d.line([(0, i), (W, i)], fill=(c, c + 2, c + 9))
    body, footf = F(34 if len(lines) > 2 else 38, MED), F(25, REG)
    blines = [(part, ln.startswith("\u2022")) for ln in lines for part in (wrap(d, ln, body, 1560) + [None])]
    flines = wrap(d, foot, footf, 1560) if foot else []
    total = (70 if kicker else 0) + 150 + 50 + sum(48 if p else 12 for p, _ in blines) + (40 + 36 * len(flines) if flines else 0)
    y = max(90, (H - total) // 2)
    if kicker:
        d.text((180, y), kicker.upper(), font=F(30, DEMI), fill=ACCENT)
        y += 70
    d.text((175, y), title, font=F(96, BOLD), fill=INK)
    y += 150
    d.rectangle([180, y, 300, y + 6], fill=ACCENT)
    y += 50
    for part, bullet in blines:
        if part is None:
            y += 12
            continue
        d.text((180, y), part, font=body, fill=(205, 210, 220) if bullet else INK)
        y += 48
    if flines:
        y += 40
        d.line([(180, y - 16), (1740, y - 16)], fill=(60, 66, 80), width=2)
        for part in flines:
            d.text((180, y), part, font=footf, fill=MUTED)
            y += 36
    return im

# ---------------------------------------------------------------- render
_cache = {}
def src_frame(t):
    i = max(0, bisect.bisect_right(ft, t) - 1)
    name = frames[i]["f"]
    if name not in _cache:
        if len(_cache) > 8:
            _cache.clear()
        im = Image.open(os.path.join(BUILD, "frames", name)).convert("RGB")
        if im.size != (W, H):
            im = im.resize((W, H), Image.LANCZOS)
        _cache[name] = im
    return name, _cache[name]

os.makedirs(os.path.dirname(OUT), exist_ok=True)
ff = subprocess.Popen(["ffmpeg", "-y", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "rgb24", "-s", f"{W}x{H}", "-r", str(FPS), "-i", "-",
                       "-f", "lavfi", "-i", "anullsrc=channel_layout=stereo:sample_rate=48000", "-shortest",
                       "-c:v", "libx264", "-preset", "slow", "-crf", "16", "-pix_fmt", "yuv420p", "-movflags", "+faststart",
                       "-c:a", "aac", "-b:a", "96k", OUT], stdin=subprocess.PIPE)
written = 0
def emit(im):
    global written
    ff.stdin.write(im.tobytes())
    written += 1

def emit_card(im, secs, fade=0.6):
    n = int(secs * FPS)
    black = Image.new("RGB", (W, H), (0, 0, 0))
    k = int(fade * FPS)
    for i in range(n):
        a = min(1.0, (i + 1) / k, (n - i) / k)
        emit(Image.blend(black, im, a) if a < 1 else im)

title = card("Factory Workbench",
             ["A workbench that builds, proves and activates its own orchestration upgrades — under a protected kernel and human approval."],
             kicker="Operator walkthrough",
             foot="Recorded from the real running system: Lean kernel, SQLite journal, sandboxed builds, proof replay and release gates are real. "
                  "Model inference is mocked by a deterministic fake Codex CLI (given a fixed 6 s response time so work is visible), and every model output is labelled as such.")
emit_card(title, 6.0)

cues = []      # (start, end, text) in output seconds
chapters = []  # (start, scene)
SCENE_NAMES = {"signin": "One-click sign-in", "home": "The workbench", "job": "A durable, reviewed job", "improve": "Improve this workbench",
               "evaluate": "P0 builds and verifies its successor", "release": "Release review",
               "activate": "Approval and activation", "after": "After activation: pinning and parallel reviews"}
layers = {}
prev_key, prev_img, prev_cap, cap_changed_at = None, None, None, 0.0
out_t = 0.0
for (s0, s1, speed, cap, sub, scene) in segs:
    dur = (s1 - s0) / speed
    n = max(1, int(round(dur * FPS)))
    key = (cap, sub, speed)
    if key not in layers:
        layers[key] = caption_layer(cap, sub, speed)
    if cap != prev_cap:
        cap_changed_at = out_t
        prev_cap = cap
        if cap:
            cues.append([out_t + 6.0, out_t + 6.0, cap + ("\n" + sub if sub else "")])
    if cues and cap:
        cues[-1][1] = out_t + 6.0 + (max(1, int(round(dur * FPS))) / FPS)
    if not chapters or chapters[-1][1] != scene:
        chapters.append((out_t + 6.0, scene))
    for i in range(n):
        st = s0 + (i / FPS) * speed
        name, base = src_frame(st)
        age = out_t + i / FPS - cap_changed_at
        alpha = min(1.0, age / 0.35)
        fkey = (name, key, round(alpha, 2))
        if fkey != prev_key:
            img = base.convert("RGBA")
            lay = layers[key]
            if alpha < 1:
                lay = lay.copy()
                lay.putalpha(lay.getchannel("A").point(lambda v: int(v * alpha)))
            img.alpha_composite(lay)
            prev_img = img.convert("RGB")
            prev_key = fkey
        emit(prev_img)
    out_t += n / FPS

# brief fade to the closing card
last = prev_img
for i in range(int(0.5 * FPS)):
    emit(Image.blend(last, Image.new("RGB", (W, H), (0, 0, 0)), (i + 1) / (0.5 * FPS)))
closing = card("What you just saw", [
    "• The running release (P0) authored and evaluated its own successor (P1)",
    "• A candidate with a proof error was rejected by the fixed verifier, then repaired in a recorded revision",
    "• Publication required build, proof replay, protected tests and both reviews for the exact payload",
    "• Approval and activation bound the exact release digest; existing jobs stayed pinned",
    "• Under P1, the independent reviews ran in parallel — both still mandatory",
], kicker="Summary",
   foot="Proved in Lean 4 about the executed kernel: K01–K12 (replayed with leanchecker --fresh). Trusted, not proved: codec, SQLite, Docker isolation, "
        "the Lean toolchain. Model reviews are judgments, not proofs. Live model inference was not used in this recording.")
emit_card(closing, 9.0)
ff.stdin.close()
ff.wait()

def ts(x, sep=","):
    h, r = divmod(x, 3600); m, r = divmod(r, 60)
    return f"{int(h):02d}:{int(m):02d}:{int(r):02d}{sep}{int(round((r % 1) * 1000)):03d}"
base = os.path.splitext(OUT)[0]
with open(base + ".srt", "w") as f:
    for i, (a, b, t) in enumerate(cues, 1):
        f.write(f"{i}\n{ts(a)} --> {ts(b)}\n{t}\n\n")
with open(base + "-chapters.txt", "w") as f:
    f.write("0:00 Introduction\n")
    for a, sc in chapters:
        if sc in SCENE_NAMES:
            f.write(f"{int(a // 60)}:{int(a % 60):02d} {SCENE_NAMES[sc]}\n")
    f.write(f"{int((written / FPS - 9) // 60)}:{int((written / FPS - 9) % 60):02d} Summary\n")
print(f"wrote {OUT}: {written} frames ({written / FPS:.1f}s)")
