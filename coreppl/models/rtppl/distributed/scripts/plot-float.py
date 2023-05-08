import matplotlib as mpl
mpl.use('Agg')

from math import exp,log
from datetime import datetime
import matplotlib.pyplot as plt
import numpy as np
import os
import struct
import shutil
import sys

def read_dists(f):
    with open(f, "rb") as f:
        data = f.read()

    dists = []
    ofs = 0
    while ofs < len(data):
        sz, ts = struct.unpack("=qq", data[ofs:ofs+16])
        ofs += 16
        samplesz = 16
        nsamples = int((sz-8)/samplesz)
        samples = []
        for i in range(nsamples):
            s, w = struct.unpack("=dd", data[ofs:ofs+samplesz])
            samples.append((w, s))
            ofs += samplesz
        dists.append((ts, samples))
    return dists

src = sys.argv[1]
dists = read_dists(src)
if not os.path.exists("plots"):
    os.mkdir("plots")
w = 0.01
now = datetime.now()
target = f'plots/{now.strftime("%Y%m%d-%H%M%S")}'
os.mkdir(target)
for i, dist in enumerate(dists):
    ts, samples = dist
    values, weights = zip(*samples)
    fig, axs0 = plt.subplots(1)
    weights = np.array(list(map(exp, weights)))
    axs0.hist(values, bins=np.arange(0.0, 2.0, w), rwidth=0.9, weights=weights)
    axs0.set_xlabel("x")
    axs0.set_ylabel("probability")
    fig.savefig(f"{target}/{i:04}.png")
