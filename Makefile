.PHONY: clean

main.native: main.ml compile.sh evm2.ml evm2.mli big.ml
	./compile.sh
evm2.ml evm2.mli: extract.v evm2.vo Makefile
	coqc extract.v
	mv List.ml CoqList.ml
	mv List.mli CoqList.mli
	mv Nat.ml CoqNat.ml
	mv Nat.mli CoqNat.mli
	sed -i -- 's/List/CoqList/g' evm2.ml evm2.mli
	sed -i -- 's/open Nat/open CoqNat/g' evm2.ml
	sed -i -- 's/Nat/CoqNat/g' BinPosDef.ml BinPosDef.mli BinPos.ml BinPos.mli
evm2.vo: evm2.v Makefile
	coqc evm2.v

clean:
	rm -f Ascii.ml Ascii.mli BinNat.ml BinNat.mli BinNums.ml BinNums.mli BinPos.ml BinPos.mli
	rm -f Bool.ml Bool.mli Compare_dec.ml Compare_dec.mli Datatypes.ml Datatypes.mli
	rm -f Div2* EqNat* Logic* NPeano* Peano* Specif* String* Nat* CoqNat* main evm2.mli evm2.vo evm2.ml extract.vo extract.glob evm2.glob
	rm -f BinPosDef* List* CoqList* main.native main.byte .evm2.aux .extract.aux
	rm -rf _build
	rm -f *~
