# Instructions for Artifact Evaluation of APIphany

## Prerequisites

1. Download and install VMware workstation player: https://www.vmware.com/products/workstation-player.html
2. Download the artifact virtual machine image
3. Run the virtual machine image inside VMware workstation player. The username is `apiphany` and the password is `apiphany!artifact`.

## Getting Started
First, please go to https://www.gurobi.com/downloads/end-user-license-agreement-academic/
and apply for a new academic license.
Once you get the new license, run `grbgetkey <your license key>`.

Now please proceed to kick-the-tires stage.

```bash
cd ~/rest_api_synthesis
git pull origin coverages
. apiphany_venv/bin/activate

make generate-full-exclude EXP_NAME=apiphany_artifact
make kick-the-tires EXP_NAME=apiphany_artifact
```
It takes about 20min to finish this small benchmark suite.
Then, you inspect the results by running

```bash
python apiphany/bench.py . --data-dir experiment_data --print-results apiphany_artifact --print-csv
csvlook results.csv -I
```
The expected results look like

| API       | ID     | Description                                   | AST  | n_f | n_p | n_g | t_Total | t_RE     | r_orig | r_RE | # cands | r_RE^TO |
| --------- | ------ | --------------------------------------------- | ---- | --- | --- | --- | ------- | -------- | ------ | ---- | ------- | ------- |
| slack     |  1.5   |  Retrieve emails of all members in a channel  |  10  |  2  |  3  |  0  |  2.9    |  0.1     |  865   |  6   |  19406  |  6      |
| stripe    |  2.1*  |  Subscribe to a product for a customer        |  9   |  2  |  2  |  0  |  14.1   |  0.2     |  657   |  2   |  5719   |  2      |
| squareapi |  3.1   |  List invoices that match a location id       |  4   |  1  |  1  |  0  |  0.2    |  $<$0.1  |  2     |  1   |  9653   |  1      |

If you are able to get similar results as above, you should be good to run the complete experiment.

## Step-by-step Instructions
1. Parse and analyze witnesses
```bash
make generate-full-exclude EXP_NAME=apiphany_artifact
```

2. Generate programs
```bash
make run-full-exclude EXP_NAME=apiphany_artifact REPEAT_EXP=3
```

3. Run ablations
To get the results for `APIphany-Syn`, run

```bash
make generate-full-exclude EXP_NAME=apiphany_syntactic ARGS="--syntactic-only"
make run-full-exclude EXP_NAME=apiphany_syntactic REPEAT_EXP=3 ARGS="--syntactic-only"
```
The virtual machine might run out of memory during this experiment,
feel free to ignore the warning and continue the run.

To get the results for `APIphany-Loc`, run

```bash
make generate-full-exclude EXP_NAME=apiphany_location ARGS="--no-merge"
make run-full-exclude EXP_NAME=apiphany_location REPEAT_EXP=3 ARGS="--no-merge"
```

It takes many hours to finish these ablation experiments.

4. Generate tables and figures
With all data on hand, now we generate Tab 1, 2 and Fig 13, 14.
- Fig 13
```bash
make plot-solved EXP_NAME=apiphany_artifact EXPS="apiphany_artifact apiphany_syntactic apiphany_location" REPEAT_EXP=3
```
The result is available as `apiphany/solved.png`.

- Fig 14
```bash
make plot-ranks EXP_NAME=apiphany_artifact REPEAT_EXP=3
```
The result is available as `apiphany/apiphany_artifact_ranks.png`.

Next, let us switch to an inner directory by
```bash
cd apiphany
```
The tables and figures can be reproduced with the following commands.

- Tab 1
```bash
python bench.py . \
    --exp-name apiphany_artifact \
    --data-dir ../experiment_data \
    --method-coverage 1.0 \
    --uncovered exclude \
    --repeat-exp 3 \
    --with-partials \
    --print-small \
    --print-csv \
    --print-api-info \
    --cache
```
The results can be viewed by
```bash
csvlook api_info.csv -I
```

- Tab 2:
```bash
python bench.py . \
    --exp-name apiphany_artifact \
    --data-dir ../experiment_data \
    --method-coverage 1.0 \
    --uncovered exclude \
    --repeat-exp 3 \
    --with-partials \
    --print-small \
    --print-csv \
    --print-results apiphany_artifact \
    --cache
```
The result can be viewed by
```bash
csvlook results_short.csv -I
```

- Tab 3
Tab 3 is in the appendix and it is an extended version of Tab 2. Tab 3 can be generated from
```bash
python bench.py . \
    --exp-name apiphany_artifact \
    --data-dir ../experiment_data \
    --method-coverage 1.0 \
    --uncovered exclude \
    --repeat-exp 3 \
    --with-partials \
    --print-csv \
    --print-results apiphany_artifact \
    --cache
```
The result can be viewed by
```bash
csvlook results.csv -I
```

## Run New Queries
You may run your own queries by adding benchmarks into `apiphany/benchmarks/suites.py`.
This file includes three large benchmark suites for `slack`, `stripe`, and `squareapi` respectively.
To add a new query, you need to first pick an API.
For example, if you want to add a new query for Slack API, then add an entry into the `slack_benchmarks`.
The entry added should be a `Benchmark` object, which is defined in `apiphany/benchmarks/benchmark.py`.
To construct a `Benchmark` object, you need to provide
```python
    Benchmark(
        name,         # benchmark name
        desc,         # benchmark description
        source,       # a source link (you may provide an empty string)
        inputs,       # a dictionary mapping from arg names to arg types (in semantic type)
        output,       # a semantic type for the return values
        solutions,    # expected solutions, written in `Program` object (defined in `apiphany/program/program.py`)
        is_effectful) # a boolean value that indicates whether this benchmark modifies the internal state or not
```
After adding the benchmark, you may go back to `~/rest_api_synthesis` and run
```bash
python apiphany/bench.py . \
    --exp-name apiphany_artifact \
    --data-dir ../experiment_data \
    --method-coverage 1.0 \
    --uncovered exclude \
    --repeat-exp 3 \
    --with-partials \
    --suites <your selected API> \
    --benchmarks <your benchmark name>
```
Note: don't forget the content between `<...>` with the actual names before you run.

## Code Structure

The source code of APIphany is included in the virtual machine.
At a top level, the implementation of APIphany is divided into four parts:
- infrastructure: the infra code includes the implementation of types, expressions and programs. The implementation lies in `apiphany/program`, `apiphany/schemas` and `apiphany/witnesses`,
- parse and type inference: this part of code is provided in `apiphany/openapi` and `apiphany/analyzer`.
- program synthesis: a synthesizer includes encoding programs into ILP constraints, decoding ILP results into programs, getting programs of different path lengths in parallel, and so on. The code is available in `apiphany/synthesizer`.
- retrospective execution: this is implemented in Rust and the code is available in `src`.

## Run a New API

This is a bit out of scope of this artifact evaluation, but we would like to provide instructions on
how to apply APIphany to other REST APIs for anyone that is interested in this.

1. Select an API that has an OpenAPI specification and ensure that it is easy for you to collect witnesses.
For example, an API has a web interface that uses the same REST API it provides and
you may use Google Chrome to record all network traffic when you create test data with the web interface.

2. Fine tune your witnesses. If you want APIphany to infer more accurate semantic types,
you need to provide high-quality witnesses. Here are some tips that might help you to collect high-quality witnesses.
First, expand your witness set to cover as many methods as possible;
Second, expand your witness set to use more data in your domain;
Third, expand your witness set to use more optional arguments correctly.

3. Write a config file. Example config files are available in `apiphany/configs`.
In this configuration file, you need to provide
- `log_file`: the witnesses you collected
- `doc_file`: the OpenAPI doc for your selected API
- `hostname`: the host name for your selected API
- other fields you may use the same settings as ours.

4. Run and inspect the inferred semantic types.
You may need to repeat step 2 and 4 many times until you get some satisfied type inference results.
In this step, you may randomly sample some methods and see whether APIphany infers proper semantic types for them.
If not, it may indicate that your witness set does not provide enough information,
or, some methods in your witness set is too general and you may consider adding that method/field into the blacklist.

5. Once you get satisfying semantic types, you can follow the steps in `Run a new query`
to add queries for your new API.

## Troubleshooting
> If you see the error message `/bin/bash: maturin: command not found`,
it means the tool `maturin` is not installed in the current environment.

**Solution**: Please go to `~/rest_api_synthesis` and run `. apiphany_venv/bin/activate`.
Then you may run the command without errors.

> If you see error messages like `TypeError: cannot pickle 'PyCapsule' object`,
it means there is some problem with the Gurobi license.

**Solution**: We apologize for having such issue. We have pre-installed a license on the machine,
please try the following two ways:
- Delete the `~/gurobi.lic` file and then run `grbgetkey c50fb4be-9b97-11ec-ad7e-0242ac120004`.
If it does not complain that this license is used elsewhere, you are fine to rerun the experiments.
- Please go to https://www.gurobi.com/downloads/end-user-license-agreement-academic/.
Apply for a free academic license and follow the instructions to install that license.

## Dependencies

This project is structured as a combined Rust/Python project (Rust is used for RE).
To build all the necessary components:

1. Install [maturin](https://github.com/PyO3/maturin).
2. Create a virtualenv and install all the Python requirements into the venv.
3. From the root directory, run `maturin develop --release --strip`.
4. The bench script should now be runnable from within the `apiphany` directory.
