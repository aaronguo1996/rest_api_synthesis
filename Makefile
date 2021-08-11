.PHONY: default

.PHONY: clean build run

build:
	maturin develop

clean:
	rm -f apiphany.cpython-39-darwin.so
