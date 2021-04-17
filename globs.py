from collections import defaultdict
import os

from synthesizer.synthesizer import Synthesizer

def init_synthesizer(doc, configuration, analyzer, exp_dir):
    synthesizer = Synthesizer(doc, configuration, analyzer, exp_dir)
    synthesizer.init()
    return synthesizer

def get_petri_net_data(syn):
    encoder_path = os.path.join(syn._exp_dir, "../encoder.txt")
    with open(encoder_path, "r") as f:
        numbers = []
        line = f.readline()
        while line:
            numbers.append(int(line))
            line = f.readline()

    return numbers[0], numbers[1]

def get_solution_strs(syn, solutions):
    return [r.pretty(syn._entries, 0) for r in solutions]
