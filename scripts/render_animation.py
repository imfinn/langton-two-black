#!/usr/bin/env python3
"""Render finite, illustrative Langton-ant runs for the README.

This program is outside the Lean proof dependency graph. It samples real
states, with north = +y and turn/flip/move in the order of Basic.lean.
"""
from __future__ import annotations

import hashlib
import json
import math
from dataclasses import dataclass
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont, __version__ as pillow_version

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "docs" / "assets"
WIDTH, HEIGHT = 1000, 628
DIRS = ((0, 1), (1, 0), (0, -1), (-1, 0))
EXAMPLES = (
    ("Near the ant", ((2, 1), (-3, 5))),
    ("Across the grid", ((-6, 4), (5, -3))),
    ("Another arrangement", ((6, -4), (-10, 0))),
)
EARLY = list(range(0, 256, 8))
EXPLORE = list(range(400, 12_000, 500))
LATE_START = 35_000
LATE = [LATE_START + 26 * i for i in range(45)]
TIMES = EARLY + EXPLORE + LATE
COLORS = {
    "page": "#f7f7f2",
    "card": "#ffffff",
    "ink": "#17252c",
    "muted": "#52636b",
    "line": "#dde5e1",
    "grid": "#eef1ec",
    "teal": "#008e7b",
    "soft": "#e0f2ea",
    "white": "#fafbf7",
    "black": "#23343b",
}


def font(size: int, bold: bool = False) -> ImageFont.ImageFont:
    names = (
        ["DejaVuSans-Bold.ttf", "LiberationSans-Bold.ttf", "Arial Bold.ttf", "VeraBd.ttf"]
        if bold else
        ["DejaVuSans.ttf", "LiberationSans-Regular.ttf", "Arial.ttf", "Vera.ttf"]
    )
    directories = (
        Path("/usr/share/fonts/truetype/dejavu"),
        Path("/usr/share/fonts/truetype/liberation2"),
        Path("/System/Library/Fonts/Supplemental"),
        Path("/Library/Fonts"),
        Path(ImageFont.__file__).parent / "fonts",
        Path("C:/Windows/Fonts"),
    )
    for name in names:
        for path in [Path(name), *(directory / name for directory in directories)]:
            try:
                return ImageFont.truetype(str(path), size)
            except OSError:
                pass
    return ImageFont.load_default(size=size)


FONTS = {name: font(size, bold) for name, size, bold in (
    ("title", 40, True), ("subtitle", 19, False),
    ("panel", 19, True), ("small", 16, False),
    ("label", 16, True), ("number", 17, False), ("badge", 30, True),
)}


@dataclass(frozen=True)
class Snapshot:
    black: frozenset[tuple[int, int]]
    x: int
    y: int
    heading: int
    read_color: bool


def simulate(seeds: tuple[tuple[int, int], ...]) -> tuple[dict[int, Snapshot], dict]:
    """Sample exact finite states and check only the displayed late window."""
    black = set(seeds)
    x = y = heading = 0
    wanted = set(TIMES)
    samples: dict[int, Snapshot] = {}
    late_observations = []
    first_reads = {}
    horizon = LATE[-1] + 104
    for time in range(horizon + 1):
        point = (x, y)
        color = point in black
        if point in seeds and point not in first_reads:
            first_reads[point] = time
        if time in wanted:
            samples[time] = Snapshot(frozenset(black), x, y, heading, color)
        if time >= LATE_START:
            late_observations.append((x, y, heading, color))
        if color:
            heading = (heading - 1) % 4
            black.remove(point)
        else:
            heading = (heading + 1) % 4
            black.add(point)
        dx, dy = DIRS[heading]
        x += dx
        y += dy
    first, following = late_observations[0], late_observations[104]
    drift = (following[0] - first[0], following[1] - first[1])
    consistent = drift in ((2, 2), (2, -2), (-2, 2), (-2, -2)) and all(
        (a[0] + drift[0], a[1] + drift[1], a[2], a[3]) == b
        for a, b in zip(late_observations, late_observations[104:])
    )
    if not consistent:
        raise ValueError(f"Example {seeds} does not repeat in the displayed window")
    if len(first_reads) != 2:
        raise ValueError(f"Both initial cells should be encountered in example {seeds}")
    encoded = json.dumps(late_observations, separators=(",", ":")).encode()
    return samples, {
        "initial_black_cells": [list(point) for point in seeds],
        "initial_pose": {"position": [0, 0], "heading": "N"},
        "first_reads": [{"cell": list(point), "time": first_reads[point]} for point in seeds],
        "late_window": [LATE_START, horizon],
        "observed_104_step_drift": list(drift),
        "late_observations_consistent": consistent,
        "late_observations_sha256": hashlib.sha256(encoded).hexdigest(),
    }


def camera(samples: dict[int, Snapshot], drift: list[int], phase: str) -> tuple[float, float, int]:
    if phase == "early":
        return 0, 0, 43
    if phase == "explore":
        points = {(0, 0)}
        for time in EXPLORE:
            state = samples[time]
            points.update(state.black)
            points.add((state.x, state.y))
        xs, ys = zip(*points)
        side = max(max(xs) - min(xs), max(ys) - min(ys)) + 11
        return (min(xs) + max(xs)) / 2, (min(ys) + max(ys)) / 2, max(side, 43)
    state = samples[LATE_START]
    return state.x + 5 * drift[0], state.y + 5 * drift[1], 51


def draw_board(draw: ImageDraw.ImageDraw, state: Snapshot, seeds: tuple,
               rectangle: tuple[int, int, int, int], view: tuple[float, float, int]) -> None:
    left, top, right, bottom = rectangle
    cx, cy, cells = view
    scale = (right - left) / cells
    x_min, y_max = cx - cells / 2, cy + cells / 2

    def center(x: float, y: float) -> tuple[float, float]:
        return left + (x - x_min) * scale, top + (y_max - y) * scale

    draw.rectangle(rectangle, fill=COLORS["white"])
    spacing = 5 if scale < 4 else 1
    for x in range(math.ceil(x_min / spacing) * spacing, math.ceil(x_min + cells), spacing):
        px, _ = center(x + 0.5, 0)
        draw.line((px, top, px, bottom), fill=COLORS["grid"])
    for y in range(math.floor((y_max - cells) / spacing) * spacing, math.ceil(y_max), spacing):
        _, py = center(0, y + 0.5)
        if top <= py <= bottom:
            draw.line((left, py, right, py), fill=COLORS["grid"])

    half = max(0.55, scale * 0.44)
    for x, y in state.black:
        px, py = center(x, y)
        if left + half <= px <= right - half and top + half <= py <= bottom - half:
            draw.rectangle((px - half, py - half, px + half, py + half), fill=COLORS["black"])
    for x, y in seeds:
        px, py = center(x, y)
        radius = max(scale * 0.7, 3.5)
        if left + radius <= px <= right - radius and top + radius <= py <= bottom - radius:
            draw.rectangle((px - radius, py - radius, px + radius, py + radius),
                           outline=COLORS["teal"], width=2)

    px, py = center(state.x, state.y)
    dx, dy = DIRS[state.heading]
    radius = max(scale * 0.9, 5)
    if left + radius <= px <= right - radius and top + radius <= py <= bottom - radius:
        forward = (dx, -dy)
        normal = (-forward[1], forward[0])
        triangle = [(px + radius * forward[0], py + radius * forward[1])]
        for side in (-1, 1):
            triangle.append((px - radius * 0.6 * forward[0] + side * radius * 0.65 * normal[0],
                             py - radius * 0.6 * forward[1] + side * radius * 0.65 * normal[1]))
        draw.polygon(triangle, fill=COLORS["teal"])
    draw.rectangle(rectangle, outline=COLORS["line"], width=1)


def render(time: int, examples: list, phase: str) -> Image.Image:
    image = Image.new("RGB", (WIDTH, HEIGHT), COLORS["page"])
    draw = ImageDraw.Draw(image)
    draw.text((24, 22), "Two black cells. Anywhere.", fill=COLORS["ink"], font=FONTS["title"])
    draw.text((26, 76), "Three starts on an infinite grid", fill=COLORS["muted"], font=FONTS["subtitle"])
    draw.rounded_rectangle((891, 22, 976, 80), radius=16, fill=COLORS["soft"])
    draw.text((904, 31), "104", fill=COLORS["teal"], font=FONTS["badge"])
    label = {"early": "01  Two initial cells", "explore": "02  Exploring and painting",
             "late": "03  Later: highway close-up"}[phase]
    draw.text((26, 111), label, fill=COLORS["teal"], font=FONTS["label"])
    draw.text((818, 110), f"t = {time:,}", fill=COLORS["muted"], font=FONTS["number"])

    for i, (title, seeds, samples, metadata, views) in enumerate(examples):
        left = 24 + 324 * i
        draw.rounded_rectangle((left, 148, left + 304, 548), radius=14,
                               fill=COLORS["card"], outline=COLORS["line"], width=1)
        draw.text((left + 14, 163), title, fill=COLORS["ink"], font=FONTS["panel"])
        draw_board(draw, samples[time], seeds, (left + 14, 200, left + 290, 476), views[phase])
        coordinate_text = "  +  ".join(f"({x}, {y})" for x, y in seeds)
        draw.text((left + 14, 490), coordinate_text, fill=COLORS["muted"], font=FONTS["small"])
        if phase == "late":
            vx, vy = metadata["observed_104_step_drift"]
            note = f"104 updates: shift ({vx:+d}, {vy:+d})"
        else:
            note = "Starts at (0, 0), facing north"
        draw.text((left + 14, 519), note, fill=COLORS["teal"], font=FONTS["small"])

    draw.rectangle((28, 569, 40, 581), outline=COLORS["teal"], width=2)
    draw.text((49, 566), "Initial cells", fill=COLORS["muted"], font=FONTS["small"])
    draw.polygon(((228, 566), (222, 580), (234, 580)), fill=COLORS["teal"])
    draw.text((244, 566), "Ant", fill=COLORS["muted"], font=FONTS["small"])
    draw.text((339, 566), "White: turn right.  Black: turn left.  Flip, then move.",
              fill=COLORS["muted"], font=FONTS["small"])
    draw.text((26, 602), "Finite illustrative simulations. Sampled times; camera changes between scenes.",
              fill=COLORS["muted"], font=FONTS["small"])
    return image


def main() -> None:
    OUTPUT.mkdir(parents=True, exist_ok=True)
    examples = []
    for title, seeds in EXAMPLES:
        samples, metadata = simulate(seeds)
        views = {phase: camera(samples, metadata["observed_104_step_drift"], phase)
                 for phase in ("early", "explore", "late")}
        examples.append((title, seeds, samples, metadata, views))
    poster = render(0, examples, "early")
    poster.save(OUTPUT / "two-black.png", optimize=True)
    palette = poster.quantize(colors=64, method=Image.Quantize.MEDIANCUT)
    frames, durations = [], []
    for time in TIMES:
        phase = "early" if time in EARLY else "explore" if time in EXPLORE else "late"
        frame = render(time, examples, phase)
        frames.append(frame.quantize(palette=palette, dither=Image.Dither.NONE))
        duration = {"early": 130, "explore": 140, "late": 100}[phase]
        if time in (EARLY[0], EXPLORE[0], LATE[0]):
            duration = 1100
        if time == TIMES[-1]:
            duration = 1900
        durations.append(duration)
    frames[0].save(OUTPUT / "two-black.gif", save_all=True, append_images=frames[1:],
                   duration=durations, loop=0, optimize=True, disposal=1)
    metadata = {
        "purpose": "finite README illustration; outside the Lean proof graph",
        "rule": "read, turn right on white/left on black, flip, move; north = +y",
        "renderer": "scripts/render_animation.py",
        "renderer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "pillow_version": pillow_version,
        "dimensions": [WIDTH, HEIGHT],
        "sample_times": TIMES,
        "durations_ms": durations,
        "duration_ms": sum(durations),
        "examples": [dict(title=title, **data) for title, _, _, data, _ in examples],
        "files": {name: {"bytes": (OUTPUT / name).stat().st_size,
                           "sha256": hashlib.sha256((OUTPUT / name).read_bytes()).hexdigest()}
                  for name in ("two-black.gif", "two-black.png")},
    }
    (OUTPUT / "animation.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(json.dumps({"frames": len(frames), "duration_ms": sum(durations),
                      "files": metadata["files"],
                      "drifts": [entry[3]["observed_104_step_drift"] for entry in examples]}, indent=2))


if __name__ == "__main__":
    main()
