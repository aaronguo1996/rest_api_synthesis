.PHONY: default

.PHONY: clean build run

build:
	maturin develop

run:
	cd apiphany && ./bench.py ../../rest-api-synthesis-paper --bench benchmarks/square_benchmark.json

clean:
	rm -f apiphany/apiphany.cpython-39-darwin.so
