from collections import defaultdict
import concurrent.futures as cf
import os
import pebble
import time

from synthesizer.hypergraph_encoder import HyperGraphEncoder
from synthesizer.petrinet_encoder import PetriNetEncoder
from synthesizer.ilp_encoder import ILPetriEncoder
from synthesizer.utils import DEFAULT_LENGTH_LIMIT
import globs

def run_encoder(synthesizer, inputs, outputs, path_len):
    input_map = defaultdict(int)
    for _, typ in inputs.items():
        input_map[typ.name] += 1

    output_map = defaultdict(int)
    for typ in outputs:
        output_map[typ.name] += 1
        
    solver_type = synthesizer._config["synthesis"]["solver_type"]
    if solver_type == "petri net":
        encoder = ILPetriEncoder({})
    elif solver_type == "hypergraph":
        encoder = HyperGraphEncoder({})
    else:
        raise Exception("Unknown solver type in config")

    for e in synthesizer._unique_entries.values():
        encoder._add_transition(e)

    # write encoder stats to file
    if path_len == 1:
        encoder_path = os.path.join(synthesizer._exp_dir, "../encoder.txt")
        with open(encoder_path, "w") as f:
            f.write(str(len(encoder._net.place())))
            f.write("\n")
            f.write(str(len(encoder._net.transition())))

    solutions = set()
    start = time.time()
    path = encoder.get_length_of(path_len, input_map, output_map)
    while path is not None:
        # print("Finding a path", path,"in", time.time() - start, "seconds at path length", path_len, flush=True)

        end = time.time()
        print(path)
        programs, perms = synthesizer._generate_solutions(
            path_len, inputs, outputs, path, end - start
        )
        solutions = solutions.union(set(programs))
        if programs is not None:
            encoder.block_prev(perms)
            path = encoder.solve()

    # print("Finished encoder running for path length", path_len, 
    #     "after time", time.time() - start, flush=True)

def spawn_encoders(synthesizer, inputs, outputs, solver_num, timeout=500):
    with pebble.ProcessPool(max_workers=solver_num) as pool:
        futures = [pool.schedule(run_encoder, args=(synthesizer, inputs, outputs, i), timeout=timeout)
            for i in range(DEFAULT_LENGTH_LIMIT + 1)]
        
        for i, future in enumerate(futures):
            try:
                future.result()
                # print(f"Completed for path length {i}")
            except cf.TimeoutError:
                pass
                # print(f"Killed path length {i} due to timeout")
