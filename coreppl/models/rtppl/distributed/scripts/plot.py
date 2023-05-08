from PIL import Image
from datetime import datetime
from matplotlib.widgets import Slider, RadioButtons
import numpy as np
import matplotlib.pyplot as plt
import bisect
import math
import os
import struct
import subprocess
import sys

def read_opt_floats(f):
    try:
        with open(f, mode="rb") as file:
            content = file.read()

        tsvs = []
        ofs = 0
        while ofs < len(content):
            ts, x, y, direction, flDist, frDist, rlDist, rrDist, lDist, rDist, speed = struct.unpack("=qdddddddddd", content[ofs:ofs+88])
            ofs += 88
            # Convert RPM to m/s
            speed = speed * 0.35 / 60.0
            # Apply modulo to the provided direction
            direction = direction % (2*math.pi)
            tsvs.append((ts, [x, y, direction, flDist, frDist, rlDist, rrDist, lDist, rDist, speed]))
        return sorted(tsvs, key=lambda x: x[0])
    except FileNotFoundError:
        print("did not find true values file")
        return None

def read_dists(f, nfields):
    with open(f, mode="rb") as file:
        content = file.read()

    dists = []
    ofs = 0
    while ofs < len(content):
        sz, ts = struct.unpack("=qq", content[ofs:ofs+16])
        ofs += 16
        if len(content) - ofs < sz - 8:
            print(f"Warning: incomplete input from {f} after reading {len(dists)} distributions")
            break
        samplesz = (nfields + 1) * 8
        nsamples = int((sz - 8) / samplesz)
        samples = []
        for i in range(nsamples):
            w, = struct.unpack("d", content[ofs:ofs+8])
            ofs += 8
            v = []
            for j in range(nfields):
                x, = struct.unpack("d", content[ofs:ofs+8])
                v.append(x)
                ofs += 8
            samples.append((math.exp(w), v))
        dists.append((ts, samples))
    return dists

def read_pos_dists(f):
    return sorted(read_dists(f, 3), key=lambda x: x[0])

def read_float_dists(f):
    return sorted(read_dists(f, 1), key=lambda x: x[0])

if len(sys.argv) != 2:
    print("Expected one argument: the room png file")
    sys.exit(1)
roomFile = sys.argv[1]
im = Image.open(roomFile)
rows = im.height
cols = im.width

inputs = {
    "pos": read_pos_dists("pos-pos.txt"),
    "front-left": read_float_dists("frontLeftDist-dist.txt"),
    "front-right": read_float_dists("frontRightDist-dist.txt"),
    "rear-left": read_float_dists("rearLeftDist-dist.txt"),
    "rear-right": read_float_dists("rearRightDist-dist.txt"),
    "left": read_float_dists("leftDist-dist.txt"),
    "right": read_float_dists("rightDist-dist.txt"),
    "speed": read_float_dists("speedEst-speed.txt")
}
true_vals = read_opt_floats("true-values.txt")

fig, (laxs, raxs) = plt.subplots(1, 2)
plt.subplots_adjust(bottom=0.20, wspace=0.4, hspace=0.5)
fig.set_dpi(200)
fst_ts, _ = inputs["pos"][0]
last_ts, _ = inputs["pos"][-1]
axfreq = fig.add_axes([0.25, 0.05, 0.65, 0.03])
ts_slider = Slider(
    ax=axfreq,
    label="Absolute time (s)",
    valmin=0,
    valmax=(last_ts-fst_ts)/1e9,
    valinit=0
)
rax = fig.add_axes([0.75, 0.8, 0.15, 0.15])
dist_buttons = RadioButtons (
    rax,
    ("front-left", "front-right", "rear-left", "rear-right", "left", "right", "speed"),
)

def choose_closest_after_timestamp(s, ts):
    p = bisect.bisect(s, int(ts), key=lambda x: x[0])
    if p >= len(s):
        return s[-1]
    return s[p]

def plot_dist(axs, dists, ts, true_val):
    ts, samples = choose_closest_after_timestamp(dists, ts)
    weights, values = [], []
    for w, v in samples:
        weights.append(w)
        values.append(v[0])
    weights = np.array(weights)
    w = 0.01
    axs.clear()
    axs.hist(values, bins=np.arange(0.0, 10.0, 0.05), rwidth=0.9, weights=weights)
    if true_val is not None:
        axs.axvline(x=true_val, ymin=0.99, ymax=1.0, color="green")
    axs.set_title(f"{(ts-fst_ts)/1e9}:\n#particles={len(samples)}")

def plot_pos_dist(axs, dists, ts, true_vals):
    ts, samples = choose_closest_after_timestamp(dists, ts)
    data = np.zeros([rows, cols])
    expected = (0.0, 0.0)
    for w, s in samples:
        x = int(10 * s[0])
        y = int(10 * s[1])
        expected = (expected[0]+10*s[0]*w, expected[1]+10*s[1]*w)
        if x >= 0 and x < cols and y >= 0 and y < rows:
            data[y][x] += w
    axs.clear()
    axs.imshow(data)
    # Plot the true x- and y-coordinates, if available
    if true_vals is not None:
        x = int(10 * true_vals[0])
        y = int(10 * true_vals[1])
        axs.plot(x, y, 'ro', markersize=1)
        textend = f",direction={true_vals[2]:.3f}"
    else:
        textend = ""
    axs.plot(expected[0], expected[1], 'bo', markersize=1)
    axs.imshow(im, alpha=0.5)
    axs.set_xlabel("x")
    axs.set_ylabel("y")
    axs.set_title(f"{(ts-fst_ts)/1e9}:\n#particles={len(samples)}{textend}")

def update(ts, label):
    if true_vals is not None:
        _, tv = choose_closest_after_timestamp(true_vals, ts)
    else:
        tv = None

    # Update distribution plots to the one most recently occuring prior to
    # or at the given timestamp (relative to the first position estimation).
    if label == "front-left":
        idx = 3
    elif label == "front-right":
        idx = 4
    elif label == "rear-left":
        idx = 5
    elif label == "rear-right":
        idx = 6
    elif label == "left":
        idx = 7
    elif label == "right":
        idx = 8
    elif label == "speed":
        idx = 9
    else:
        print(f"Unknown label: {label}")
    laxs.set_ylabel("probability")
    if tv is not None:
        true_val = tv[idx]
    else:
        true_val = None
    plot_dist(laxs, inputs[label], ts, true_val)

    # Update position image
    plot_pos_dist(raxs, inputs["pos"], ts, tv)

    fig.canvas.draw_idle()

def update_dist(label):
    update(fst_ts + ts_slider.val * 1e9, label)

def update_slider(rel_ts):
    update(fst_ts + rel_ts * 1e9, dist_buttons.value_selected)

update_slider(0)

ts_slider.on_changed(update_slider)
dist_buttons.on_clicked(update_dist)
plt.show()
