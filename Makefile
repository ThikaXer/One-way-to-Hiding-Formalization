
O2H.zip :
	rm -rf tmp $@
	mkdir -p tmp/Oneway2Hiding
	rm -f document/*~
	cp -r *.thy ROOT document Kraus_Maps tmp/Oneway2Hiding/
	cd tmp && zip -r ../$@ Oneway2Hiding

