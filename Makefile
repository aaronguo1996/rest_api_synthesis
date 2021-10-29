.PHONY: default

.PHONY: clean build run

# default directory for storing the collected witnesses
DEFAULT_EXP_DIR=default_apiphany
# default experiment name
EXP_NAME=apiphany_exp
# benchmark script
BENCH_SRC=bench.py
BENCH_EXE=python $(BENCH_SRC)
# reps
REPEAT_EXP=3
uncovered_exclude=exclude
uncovered_syntactic=default-to-syntactic
coverage_onethird=0.33
coverage_twothirds=0.67
coverage_full=1.0
word-dot=$(word $2,$(subst _, ,$1))

build:
	maturin develop --release --strip

run_full_exclude run_full_syntactic run_onethird_exclude run_onethird_syntactic run_twothirds_exclude run_twothirds_syntactic: build
	cd apiphany && $(BENCH_EXE) . --data-dir ../experiment_data \
		--exp-name $(EXP_NAME) \
		--generate-witness \
		--method-coverage $(coverage_$(call word-dot,$@,2)) \
		--uncovered $(uncovered_$(call word-dot,$@,3)) \
		--repeat-exp $(REPEAT_EXP)
	cd ..

clean:
	rm -f apiphany/apiphany.*.so
	cd experiment_data && for dir in *; do \
		[ "$$dir" = ${DEFAULT_EXP_DIR} ] && continue; \
		rm -rf "$$dir"; \
	done
