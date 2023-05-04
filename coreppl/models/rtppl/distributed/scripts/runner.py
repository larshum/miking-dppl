import json
import os
import signal
import subprocess
import sys
import time

procs = []

def handler(sig, frame):
    print("Killing remaining processes");
    for proc in procs:
        proc.send_signal(signal.SIGINT)
        try:
            proc.wait(0.5)
        except subprocess.TimeoutExpired:
            proc.terminate()
            proc.wait()
    sys.exit(0)

def read_network(file):
    with open(file) as f:
        data = json.loads(f.read())

    # We ignore the brake task and any connections involving it
    tasks = data["tasks"]

    # We only run the relay to deliver data between tasks
    ignored_conn = set(data["sensors"] + data["actuators"])
    relays = {}
    for c in data["connections"]:
        if c["from"] in ignored_conn or c["to"] in ignored_conn:
            pass
        else:
            if not c["from"] in relays:
                relays[c["from"]] = []
            relays[c["from"]].append(c["to"])

    return {
        "tasks": tasks,
        "relays": relays
    }

signal.signal(signal.SIGINT, handler)

map_file = sys.argv[1]
nw = read_network("network.json")
for src, dsts in nw["relays"].items():
    cmd = ["./relay", src] + dsts
    print(cmd)
    procs.append(subprocess.Popen(cmd, stdin=None, stdout=None, stderr=None))
for task in nw["tasks"]:
    cmd = [f"./{task}", map_file]
    print(cmd)
    procs.append(subprocess.Popen(cmd, stdin=None, stdout=None, stderr=None, env={"OCAMLRUNPARAM": "b"}))

while True:
    live = []
    for proc in procs:
        if proc.poll():
            proc.kill()
            proc.wait()
            print(f"Process {proc.args} died")
        else:
            live.append(proc)
    procs = live
    time.sleep(1)
