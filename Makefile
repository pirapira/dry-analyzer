.PHONY: clean

main.native: main.ml compile.sh evm.ml evm.mli big.ml
	./compile.sh
evm.ml evm.mli: extract.v evm.vo Makefile
	coqc extract.v
	mv List.ml CoqList.ml
	mv List.mli CoqList.mli
	mv Nat.ml CoqNat.ml
	mv Nat.mli CoqNat.mli
	sed -i -- 's/List/CoqList/g' evm.ml evm.mli
	sed -i -- 's/open Nat/open CoqNat/g' evm.ml
	sed -i -- 's/Nat/CoqNat/g' BinPosDef.ml BinPosDef.mli BinPos.ml BinPos.mli
evm.vo: evm.v Makefile
	coqc evm.v

clean:
	rm -f Ascii.ml Ascii.mli BinNat.ml BinNat.mli BinNums.ml BinNums.mli BinPos.ml BinPos.mli
	rm -f Bool.ml Bool.mli Compare_dec.ml Compare_dec.mli Datatypes.ml Datatypes.mli
	rm -f Div2* EqNat* Logic* NPeano* Peano* Specif* String* Nat* CoqNat* main evm.mli evm.vo evm.ml extract.vo extract.glob evm.glob
	rm -f BinPosDef* List* CoqList* main.native main.byte .evm.aux .extract.aux
	rm -rf _build
	rm -f *~
