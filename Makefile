.PHONY: default

.PHONY: clean build run

SHELL=/bin/bash # Use bash syntax

# default directory for storing the collected witnesses
DEFAULT_EXP_DIR=default_apiphany
# default experiment name
EXP_NAME=apiphany_exp
# benchmark script
BENCH_SRC=bench.py
BENCH_EXE=python $(BENCH_SRC)
# reps
REPEAT_EXP=1
# experiments
EXPS=apiphany_repeat apiphany_no_semantic apiphany_no_merge
# optional args
ARGS=
# params
uncovered_exclude=exclude
uncovered_syntactic=default-to-syntactic
coverage_onethird=0.33
coverage_twothirds=0.67
coverage_full=1.0
word-dash=$(word $2,$(subst -, ,$1))

build:
	maturin develop --release --strip

generate-full-exclude generate-full-syntactic generate-onethird-exclude generate-onethird-syntactic generate-twothirds-exclude generate-twothirds-syntactic: build
	cd apiphany && $(BENCH_EXE) . --data-dir ../experiment_data \
		--exp-name $(EXP_NAME) \
		--generate-witness \
		--generate-witness-only \
		--method-coverage $(coverage_$(call word-dash,$@,2)) \
		--uncovered $(uncovered_$(call word-dash,$@,3)) \
		--repeat-exp 1 \
		--with-partials \
		$(ARGS); \
	cd .. ; \

run-full-exclude run-full-syntactic run-onethird-exclude run-onethird-syntactic run-twothirds-exclude run-twothirds-syntactic: build
	rep=1 ; while [[ $$rep -le $(REPEAT_EXP) ]] ; do \
		for suite in "slack" "stripe" "squareapi" ; do \
			cd apiphany && $(BENCH_EXE) . --data-dir ../experiment_data \
				--exp-name $(EXP_NAME) \
				--method-coverage $(coverage_$(call word-dash,$@,2)) \
				--uncovered $(uncovered_$(call word-dash,$@,3)) \
				--repeat-exp $(REPEAT_EXP) \
				--suites $$suite \
				--with-partials \
				$(ARGS) ; \
			cd .. ; \
		done ; \
		((rep = rep + 1)) ; \
	done

plot-all: plot-ranks plot-solved

plot-solved:
	cd apiphany && $(BENCH_EXE) . --data-dir ../experiment_data \
		--exp-name $(EXP_NAME) \
		--$@ $(EXPS)\
		--repeat-exp $(REPEAT_EXP)

plot-ranks:
	cd apiphany && $(BENCH_EXE) . --data-dir ../experiment_data \
		--exp-name $(EXP_NAME) \
		--$@ apiphany_repeat \
		--repeat-exp $(REPEAT_EXP)

clean:
	rm -f apiphany/apiphany.*.so
	cd experiment_data && for dir in *; do \
		[ "$$dir" = ${DEFAULT_EXP_DIR} ] && continue; \
		rm -rf "$$dir"; \
	done
