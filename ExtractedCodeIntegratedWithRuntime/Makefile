UNCHANGED:=ocaml-4.14-unchanged
HACKED:=ocaml-4.14-hacked-gc
BDWGC:=ocaml-4.14-bdwgc
unchanged:
	PWD=$(shell pwd)
	cd $(UNCHANGED); ./configure --prefix=$(PWD)/$(UNCHANGED)/_install  --disable-naked-pointers
	make -C $(UNCHANGED) -j
	make -C $(UNCHANGED) install

verified-gc:
	cd $(HACKED); ./configure --disable-naked-pointers
	make -C $(HACKED)/runtime -j ocamlrun ocamlrund

bdwgc:
	cd $(BDWGC); ./configure --disable-naked-pointers
	make -C $(BDWGC)/runtime -j ocamlrun ocamlrund

clean-unchanged:
	make -C $(UNCHANGED) clean

clean-bdwgc:
	make -C $(BDWGC) clean

clean-verified-gc:
	make -C $(HACKED) clean

all: unchanged verified-gc bdwgc

clean-all: clean-unchanged clean-verified-gc clean-bdwgc
