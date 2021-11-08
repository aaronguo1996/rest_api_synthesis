from collections import defaultdict
import multiprocessing
import os
# import pebble
import time
import signal
from functools import partial
import cProfile

from synthesizer.hypergraph_encoder import HyperGraphEncoder
from synthesizer.ilp_encoder import ILPetriEncoder
from synthesizer.petrinet_encoder import PetriNetEncoder
import consts
from apiphany import rust_re, translate_traces, free_up
from schemas import types

def get_results(synthesizer, analyzer, encoder, 
    repeat_time, run_re, inputs, outputs, output_map, 
    is_array_output, expected_solution, conversion_fair, solutions, path_len,
    start, re_time, path_count):
    solution_set = set()
    include_more_syntactic = True
    encoder.set_final(output_map)
    encoder.reset_syntactic()

    while include_more_syntactic:
        path = encoder.solve()
        while path is not None:
            # if path_len == 5:
            # print("Found a path", path,"in", time.time() - start, "seconds at path length", path_len, flush=True)
            end = time.time()
            # print(path)
            path_count += 1
            programs = synthesizer.generate_solutions(
                path_len, inputs, outputs, path, end - start
            )

            for p in programs:
                if p not in solution_set:
                    # print("Found a program", p, flush=True)
                    solution_set.add(p)
                    re_start = time.time()
                    if run_re:
                        cost = rust_re(analyzer, p, list(inputs.items()), is_array_output, repeat_time)
                    else:
                        cost = None
                    re_time += time.time() - re_start
                    solutions.put((path_count, time.time() - start, p, re_time, cost))

                    # # hope this can reduce the memory usage
                    # if len(solution_set) > 10**6:
                    #     return consts.SearchStatus.NOT_FOUND

                    if p == expected_solution:
                        # print("Found expected solution", flush=True)
                        solution_set.add(p)
                        return consts.SearchStatus.FOUND_EXPECTED

            encoder.block_prev()
            path = encoder.solve()

        include_more_syntactic = encoder.increment_syntactic()

    return consts.SearchStatus.NOT_FOUND

def run_encoder(synthesizer, analyzer, entries, 
    repeat_time, run_re, inputs, outputs, is_array_output,
    expected_solution, conversion_fair, prim_as_return, all_solutions, path_len):
    solutions = all_solutions[path_len]
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

    for name, e in synthesizer.unique_entries.items():
        encoder.add_transition(name, e)

    input_map = defaultdict(int)
    transformed_inputs = {}
    for name, typ in inputs.items():
        typ_name = str(typ.ignore_array())
        # double check whether the type name is available in the encoder
        # if not, default to its primitive type
        if not encoder.type_exists(typ_name):
            typ_name = typ.get_primitive_name()
            transformed_inputs[name] = typ.to_syntactic()
        else:
            transformed_inputs[name] = typ

        input_map[typ_name] += 1

    output_map = defaultdict(int)
    transformed_outputs = []
    for typ in outputs:
        typ_name = str(typ.ignore_array())
        if not encoder.type_exists(typ_name):
            typ_name = typ.get_primitive_name()
            transformed_outputs.append(typ.to_syntactic())
        else:
            transformed_outputs.append(typ)

        output_map[typ_name] += 1
 
    encoder.init(input_map, output_map, prim_as_return)
    while encoder._path_len < path_len:
        encoder.increment()
    print("input_map", input_map)
    print("output_map", output_map)

    if solutions is None:
        # temporary for rebuttal
        place_counts = {}
        for p in encoder._net.place():
            num_pre = 0
            for tr in encoder._net.pre(p.name):
                if "projection" not in tr and "filter" not in tr:
                    num_pre += 1

            num_post = 0
            for tr in encoder._net.post(p.name):
                if "projection" not in tr and "filter" not in tr:
                    num_post += 1

            num_connection = num_pre + num_post
            place_counts[p.name] = num_connection

        # get the most popular types
        max_types = sorted(place_counts, key=place_counts.get, reverse=True)
        print(max_types[:10])

        return

    # write encoder stats to file
    
    if path_len == 1:
        encoder_path = os.path.join(synthesizer.exp_dir, "encoder.txt")
        with open(encoder_path, "w") as f:
            f.write(str(len(encoder._net.place())))
            f.write("\n")
            f.write(str(len(encoder._net.transition())))
            f.write("\n")
            f.flush()

    translate_traces(entries)

    # initialize stats
    start = time.time()
    re_time = 0
    path_count = 0

    res = get_results(synthesizer, analyzer, encoder, 
        repeat_time, run_re, transformed_inputs, transformed_outputs, output_map, 
        is_array_output, expected_solution, conversion_fair, solutions, path_len,
        start, re_time, path_count)

    if res == consts.SearchStatus.NOT_FOUND and prim_as_return:
        prim_outputs = [o.to_syntactic() for o in outputs]
        prim_output_map = defaultdict(int)
        for typ in prim_outputs:
            typ_name = typ.ignore_array().get_primitive_name()
            prim_output_map[typ_name] += 1

        # try again with primitives as return values
        res = get_results(synthesizer, analyzer, encoder, 
            repeat_time, run_re, transformed_inputs, prim_outputs, prim_output_map, 
            is_array_output, expected_solution, conversion_fair, solutions, path_len,
            start, re_time, path_count)
    
    # print("Finished encoder running for path length", path_len,
    #     "after time", time.time() - start, flush=True)

    free_up()
    return res

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
            # penalize programs with conversions from semantic to syntactic
            if prog.has_conversion():
                cost += 10

            prog_list.append((syn_time, prog, re_time, cost))

        print(i, len(prog_list), flush=True)
        synthesizer._serialize_solutions(i, prog_list)
        all_path_cnt += path_cnt

    encoder_path = os.path.join(synthesizer.exp_dir, "encoder.txt")
    with open(encoder_path, "a") as f:
        f.write(str(all_path_cnt))
        f.write("\n")

def spawn_encoders(synthesizer, analyzer, entries, 
    repeat_time, run_re, inputs, outputs, is_array_output,
    solver_num, expected_solution, conversion_fair, prim_as_return, timeout=90):
    m = multiprocessing.Manager()
    all_solutions = []
    for _ in range(consts.DEFAULT_LENGTH_LIMIT + 1):
        solutions = m.Queue()
        all_solutions.append(solutions)

    pool = multiprocessing.Pool(processes=solver_num)
    results = pool.imap_unordered(
        partial(run_encoder,
                synthesizer, analyzer, entries,
                repeat_time, run_re, inputs, outputs, is_array_output,
                expected_solution, conversion_fair, prim_as_return,
                all_solutions),
        range(consts.DEFAULT_LENGTH_LIMIT + 1),
        # [5]
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