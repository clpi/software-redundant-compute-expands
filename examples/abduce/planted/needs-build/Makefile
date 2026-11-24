# planted control: the gate needs a table that this build generates
gen/table.txt:
	mkdir -p gen
	seq 1 64 | awk '{ s += $$1; print $$1, s }' > gen/table.txt
	echo built > gen/stamp
