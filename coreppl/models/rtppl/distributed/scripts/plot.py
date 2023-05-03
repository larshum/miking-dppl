from PIL import Image
from datetime import datetime
from matplotlib.widgets import Slider, RadioButtons
from math import exp
import numpy as np
import matplotlib.pyplot as plt
import bisect
import math
import os
import struct
import subprocess
import sys

def read_dists(f, nfields):
    with open(f, mode="rb") as file:
        content = file.read()

    dists = []
    ofs = 0
    while ofs < len(content):
        sz, ts = struct.unpack("=qq", content[ofs:ofs+16])
        ofs += 16
        if len(content) - ofs < sz - 8:
            print(f"Warning: incomplete input from {f}")
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
            samples.append((w, v))
        dists.append((ts, samples))
    return dists

def read_pos_dists(f):
    return sorted(read_dists(f, 3), key=lambda x: x[0])

def read_float_dists(f):
    return sorted(read_dists(f, 1), key=lambda x: x[0])

def clamp(p, n):
    if p < 0:
        return 0
    if p >= n:
        return n-1

def choose_dist(dists, ts):
    p = bisect.bisect(dists, ts, key=lambda x: x[0])
    if p < 0:
        return dists[0]
    elif p >= len(dists):
        return dists[-1]
    return dists[p]

def plot_dist(axs, dists, ts):
    _, samples = choose_dist(dists, ts)
    weights, values = [], []
    for w, v in samples:
        weights.append(exp(w))
        values.append(v[0])
    weights = np.array(weights)
    w = 0.01
    axs.clear()
    axs.hist(values, bins=np.arange(min(values), max(values) + w, w), rwidth=0.9, weights=weights)

if len(sys.argv) != 2:
    print("Expected one argument: the room png file")
    sys.exit(1)
roomFile = sys.argv[1]
im = Image.open(roomFile)
rows = im.height
cols = im.width

def plot_pos_dist(axs, dists, ts):
    _, samples = choose_dist(dists, ts)
    data = np.zeros([rows, cols])
    for w, s in samples:
        x = int(10 * s[0])
        y = int(10 * s[1])
        if x >= 0 and x < cols and y >= 0 and y < rows:
            data[y][x] += 1
    axs.imshow(data)
    axs.imshow(im, alpha=0.5)
    axs.set_xlabel("x")
    axs.set_ylabel("y")

if not os.path.exists("plots/"):
    os.mkdir("plots")

inputs = {
    "pos": read_pos_dists("pos.txt"),
    "front": read_float_dists("frontDist-dist.txt"),
    "rear": read_float_dists("rearDist-dist.txt"),
    "left": read_float_dists("leftDist-dist.txt"),
    "right": read_float_dists("rightDist-dist.txt"),
    "speed": read_float_dists("speedEst-speed.txt")
}

now = datetime.now()
target = f'plots/{now.strftime("%Y%m%d-%H%M%S")}'
os.mkdir(target)

fig, (laxs, raxs) = plt.subplots(1, 2)
plt.subplots_adjust(bottom=0.20, wspace=0.4, hspace=0.5)
fig.set_dpi(150)
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
rax = fig.add_axes([0.75, 0.7, 0.15, 0.15])
dist_buttons = RadioButtons (
    rax,
    ("front", "rear", "left", "right", "speed"),
)

def update(ts, label):
    # Update distribution plots to the one most recently occuring prior to
    # or at the given timestamp (relative to the first position estimation).
    if label == "front":
        laxs.set_xlabel("front distance (m)")
    elif label == "rear":
        laxs.set_xlabel("rear distance (m)")
    elif label == "left":
        laxs.set_xlabel("left distance (m)")
    elif label == "right":
        laxs.set_xlabel("right distance (m)")
    elif label == "speed":
        laxs.set_xlabel("speed (m/s)")
    laxs.set_ylabel("probability")
    plot_dist(laxs, inputs[label], ts)

    # Update position image
    plot_pos_dist(raxs, inputs["pos"], ts)

    fig.canvas.draw_idle()

def update_dist(label):
    update(fst_ts + ts_slider.val * 1e9, label)

def update_slider(rel_ts):
    update(fst_ts + rel_ts * 1e9, dist_buttons.value_selected)

update_slider(0)

ts_slider.on_changed(update_slider)
dist_buttons.on_clicked(update_dist)
plt.show()

#for i, (_, dist) in enumerate(inputs["pos"]):
#    fig, axs = plt.subplots(1)
#    data = np.zeros([rows, cols])
#    for (w, s) in dist:
#        # NOTE: assumes each pixel of the map represents a 10x10 cm square
#        x = int(10 * s[0])
#        y = int(10 * s[1])
#        if x >= 0 and x < cols and y >= 0 and y < rows:
#            data[y][x] += 1
#    axs.imshow(data)
#    axs.set_xlabel("x")
#    axs.set_ylabel("y")
#    axs.imshow(im, alpha=.5)
#    fig.savefig(f"{target}/{i+1:04}.png")
#    plt.close()
