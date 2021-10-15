from collections import defaultdict
import multiprocessing
import os
# import pebble
import time
import signal
from functools import partial

from synthesizer.hypergraph_encoder import HyperGraphEncoder
from synthesizer.ilp_encoder import ILPetriEncoder
from synthesizer.petrinet_encoder import PetriNetEncoder
import consts
from apiphany import rust_re, translate_traces, free_up
from schemas import types

def run_encoder(synthesizer, analyzer, entries, repeat_time, inputs, outputs, expected_solution, all_solutions, path_len):
    solutions = all_solutions[path_len]
    input_map = defaultdict(int)
    for _, typ in inputs.items():
        typ_name = str(typ.ignore_array())
        input_map[typ_name] += 1

    output_map = defaultdict(int)
    for typ in outputs:
        typ_name = str(typ.ignore_array())
        output_map[typ_name] += 1

    config = synthesizer._config
    solver_type = config[consts.KEY_SYNTHESIS][consts.KEY_SOLVER_TYPE]
    if solver_type == consts.SOLVER_PN_SMT:
        encoder = PetriNetEncoder({})
    elif solver_type == consts.SOLVER_PN_ILP:
        encoder = ILPetriEncoder({})
    elif solver_type == consts.SOLVER_HYPER:
        encoder = HyperGraphEncoder({})
    else:
        raise Exception("Unknown solver type in config")

    for name, e in synthesizer._unique_entries.items():
        encoder.add_transition(name, e)

    if solutions is None:
        # temporary for rebuttal
        place_counts = {}
        for p in encoder._net.place():
            num_pre = len([tr for tr in encoder._net.pre(p.name) if "projection" not in tr and "filter" not in tr])
            num_post = len([tr for tr in encoder._net.post(p.name) if "projection" not in tr and "filter" not in tr])
            num_connection = num_pre + num_post
            place_counts[p.name] = num_connection

        # get the most popular types
        max_types = sorted(place_counts, key=place_counts.get, reverse=True)
        print(max_types[:10])

        return

    # write encoder stats to file
    path_count = 0
    if path_len == 1:
        encoder_path = os.path.join(synthesizer._exp_dir, "encoder.txt")
        with open(encoder_path, "w") as f:
            f.write(str(len(encoder._net.place())))
            f.write("\n")
            f.write(str(len(encoder._net.transition())))
            f.write("\n")

    translate_traces(entries)

    solution_set = set()
    start = time.time()
    path = encoder.get_length_of(path_len, input_map, output_map)
    re_time = 0
    while path is not None:
        # print("Finding a path", path,"in", time.time() - start, "seconds at path length", path_len, flush=True)

        end = time.time()
        # print(path)
        path_count += 1
        programs, perms = synthesizer._generate_solutions(
            path_len, inputs, outputs, path, end - start
        )

        for p in set(programs):
            if p not in solution_set:
                solution_set.add(p)
                re_start = time.time()
                cost = rust_re(
                    analyzer, p,
                    list(inputs.items()),
                    isinstance(outputs[0], types.ArrayType),
                    repeat_time)
                re_time += time.time() - re_start
                solutions.put((path_count, time.time() - start, p, re_time, cost))


                if p == expected_solution:
                    print("Found expected solution", flush=True)
                    solution_set.add(p)
                    free_up()
                    return consts.SearchStatus.FOUND_EXPECTED

        encoder.block_prev(perms)
        path = encoder.solve()

    print("Finished encoder running for path length", path_len,
        "after time", time.time() - start, flush=True)

    free_up()
    return consts.SearchStatus.NOT_FOUND
    # raise Exception("No solution found at this length")

def collect_parallel_data(synthesizer, all_solutions):
    all_path_cnt = 0
    for i, progs in enumerate(all_solutions):
        # print(i, progs.qsize(), flush=True)
        prog_list = []
        path_cnt = 0
        while not progs.empty():
            item = progs.get_nowait()
            if item is None:
                break

            path_cnt, syn_time, prog, re_time, cost = item
            prog_list.append((syn_time, prog, re_time, cost))

        synthesizer._serialize_solutions(i, prog_list)
        all_path_cnt += path_cnt

    encoder_path = os.path.join(synthesizer._exp_dir, "encoder.txt")
    with open(encoder_path, "a") as f:
        f.write(str(all_path_cnt))
        f.write("\n")

def spawn_encoders(synthesizer, analyzer, entries, repeat_time, inputs, outputs, solver_num, expected_solution, timeout=60):
    m = multiprocessing.Manager()
    all_solutions = []
    for _ in range(consts.DEFAULT_LENGTH_LIMIT + 1):
        solutions = m.Queue()
        all_solutions.append(solutions)

    pool = multiprocessing.Pool(processes=solver_num)
    results = pool.imap_unordered(
        partial(run_encoder,
                synthesizer, analyzer, entries,
                repeat_time, inputs, outputs, expected_solution, all_solutions),
        range(consts.DEFAULT_LENGTH_LIMIT + 1),
        # [3]
    )
    while True:
        try:
            status = results.next(timeout=timeout)
            if status == consts.SearchStatus.FOUND_EXPECTED:
                pool.terminate()
                break
        except StopIteration:
            pool.terminate()
            break
        except multiprocessing.TimeoutError:
            print("Timeout", flush=True)
            pool.terminate()
            break

    pool.close()
    pool.join()

    collect_parallel_data(synthesizer, all_solutions)