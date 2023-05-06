import json
import os

def try_remove(f):
    try:
        os.remove(f)
    except FileNotFoundError:
        pass

nwfile = "network.json"
with open(nwfile, "r") as f:
    data = json.load(f)

for task in data["tasks"]:
    try_remove(task)
    try_remove(f"{task}.mc")
for conn in data["connections"]:
    src, dst = conn["from"], conn["to"]
    try_remove(src)
    try_remove(dst)
try_remove(nwfile)
