#!/bin/bash

echo "************************************************"
echo "*****     Running coverage experiments     *****"
echo "************************************************"

gen_witnesses()
{
	echo "Analyzing witnesses with coverage $1 and uncovered methods $2"
	echo "================================================"
	./bench.py . --exp-name "apiphany_coverage_$1_$2" \
		--data-dir ../experiment_data_20210707_2056 \
		--generate-witness --generate-witness-only \
		--method-coverage "$1" --uncovered "$2"
	echo "================================================"
}

gen_witnesses_prim()
{
	echo "Analyzing witnesses with coverage $1 and uncovered methods $2"
	echo "================================================"
	./bench.py . --exp-name "apiphany_coverage_$1_$2_prim" \
		--data-dir ../experiment_data_20210707_2056 \
		--generate-witness --generate-witness-only \
		--method-coverage "$1" --uncovered "$2"
	echo "================================================"
}

run_synthesis()
{
	
	echo "Generating programs under the settings of coverage $1 and uncovered methods $2"
	echo "================================================"
	./bench.py . --exp-name "apiphany_coverage_$1_$2" \
		--data-dir ../experiment_data_20210707_2056 \
		--method-coverage "$1" \
		--repeat-exp 1
	echo "================================================"
}

run_synthesis_prim()
{
	echo "Generating programs under the settings of coverage $1, uncovered methods $2 and find primitive types"
	echo "================================================"
	./bench.py . --exp-name "apiphany_coverage_$1_$2_prim" \
		--data-dir ../experiment_data_20210707_2056 \
		--method-coverage "$1" \
		--repeat-exp 1 \
		--primitive-as-return
	echo "================================================"
}

gen_witnesses 0.33 default-to-syntactic
run_synthesis 0.33 default-to-syntactic

gen_witnesses_prim 0.33 default-to-syntactic
run_synthesis_prim 0.33 default-to-syntactic

gen_witnesses 0.33 exclude
run_synthesis 0.33 exclude

gen_witnesses 0.66 default-to-syntactic
run_synthesis 0.66 default-to-syntactic

gen_witnesses_prim 0.66 default-to-syntactic
run_synthesis_prim 0.66 default-to-syntactic

gen_witnesses 0.66 exclude
run_synthesis 0.66 exclude

gen_witnesses 1.0 default-to-syntactic
run_synthesis 1.0 default-to-syntactic

gen_witnesses_prim 1.0 default-to-syntactic
run_synthesis_prim 1.0 default-to-syntactic

# gen_witnesses 1.0 exclude
# run_synthesis 1.0 exclude