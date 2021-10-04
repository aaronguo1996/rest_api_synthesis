import os

from synthesizer.synthesizer import Synthesizer

def init_synthesizer(configuration, entries, exp_dir):
    synthesizer = Synthesizer(configuration, entries, exp_dir)
    synthesizer.init()
    return synthesizer

def get_petri_net_data(exp_dir):
    encoder_path = os.path.join(exp_dir, "encoder.txt")
    with open(encoder_path, "r") as f:
        numbers = []
        line = f.readline()
        while line:
            numbers.append(int(line))
            line = f.readline()

    return numbers[0], numbers[1], numbers[2]

def get_solution_strs(solutions):
    return [r.pretty(0) for r in solutions]
