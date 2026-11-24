"""planted control: writes data/out.json (needs planted_helper from lib/)"""
import json, os
import planted_helper
os.makedirs(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data"), exist_ok=True)
json.dump({"total": planted_helper.triangle(64)}, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data", "out.json"), "w"))
