.PHONY: default

.PHONY: clean build run

build:
	maturin develop --release --strip

run:
	cd apiphany && ./bench.py ../../rest-api-synthesis-paper --bench benchmarks/square_benchmark.json

clean:
	rm -f apiphany/apiphany.*.so
