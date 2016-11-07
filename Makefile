
test:
	python3 -m doctest *.py

format:
	autopep8 --in-place --aggressive --aggressive *.py
