From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Module Info.
  Definition version := "3.8".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "32sse2".
  Definition abi := "standard".
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "src/sparch.c".
  Definition normalized := true.
End Info.

Definition _COOChunk_append : ident := 92%positive.
Definition _COOChunk_concat : ident := 96%positive.
Definition _COOChunk_free : ident := 87%positive.
Definition _COOChunk_freeAll : ident := 91%positive.
Definition _COOChunk_freeNodes : ident := 89%positive.
Definition _COOChunk_malloc : ident := 86%positive.
Definition _COOChunk_print : ident := 104%positive.
Definition _COOChunk_push : ident := 93%positive.
Definition _COOChunk_toCSR : ident := 100%positive.
Definition _COOItem_free : ident := 176%positive.
Definition _COOItem_malloc : ident := 113%positive.
Definition _CSR_dense : ident := 187%positive.
Definition _CSR_free : ident := 183%positive.
Definition _CSR_malloc : ident := 99%positive.
Definition _LLNode_free : ident := 83%positive.
Definition _LLNode_freeAll : ident := 84%positive.
Definition _LLNode_malloc : ident := 82%positive.
Definition _Matrix_free : ident := 179%positive.
Definition _Matrix_malloc : ident := 178%positive.
Definition _Matrix_toCSR : ident := 182%positive.
Definition __COOChunk : ident := 19%positive.
Definition __COOItem : ident := 8%positive.
Definition __CSRMatrix : ident := 12%positive.
Definition __LLNode : ident := 14%positive.
Definition __Matrix : ident := 4%positive.
Definition __PriorQ : ident := 23%positive.
Definition ___builtin_ais_annot : ident := 24%positive.
Definition ___builtin_annot : ident := 41%positive.
Definition ___builtin_annot_intval : ident := 42%positive.
Definition ___builtin_bswap : ident := 26%positive.
Definition ___builtin_bswap16 : ident := 28%positive.
Definition ___builtin_bswap32 : ident := 27%positive.
Definition ___builtin_bswap64 : ident := 25%positive.
Definition ___builtin_clz : ident := 29%positive.
Definition ___builtin_clzl : ident := 30%positive.
Definition ___builtin_clzll : ident := 31%positive.
Definition ___builtin_ctz : ident := 32%positive.
Definition ___builtin_ctzl : ident := 33%positive.
Definition ___builtin_ctzll : ident := 34%positive.
Definition ___builtin_debug : ident := 77%positive.
Definition ___builtin_fabs : ident := 35%positive.
Definition ___builtin_fabsf : ident := 36%positive.
Definition ___builtin_fmadd : ident := 69%positive.
Definition ___builtin_fmax : ident := 67%positive.
Definition ___builtin_fmin : ident := 68%positive.
Definition ___builtin_fmsub : ident := 70%positive.
Definition ___builtin_fnmadd : ident := 71%positive.
Definition ___builtin_fnmsub : ident := 72%positive.
Definition ___builtin_fsqrt : ident := 37%positive.
Definition ___builtin_membar : ident := 43%positive.
Definition ___builtin_memcpy_aligned : ident := 39%positive.
Definition ___builtin_read16_reversed : ident := 73%positive.
Definition ___builtin_read32_reversed : ident := 74%positive.
Definition ___builtin_sel : ident := 40%positive.
Definition ___builtin_sqrt : ident := 38%positive.
Definition ___builtin_va_arg : ident := 45%positive.
Definition ___builtin_va_copy : ident := 46%positive.
Definition ___builtin_va_end : ident := 47%positive.
Definition ___builtin_va_start : ident := 44%positive.
Definition ___builtin_write16_reversed : ident := 75%positive.
Definition ___builtin_write32_reversed : ident := 76%positive.
Definition ___compcert_i64_dtos : ident := 52%positive.
Definition ___compcert_i64_dtou : ident := 53%positive.
Definition ___compcert_i64_sar : ident := 64%positive.
Definition ___compcert_i64_sdiv : ident := 58%positive.
Definition ___compcert_i64_shl : ident := 62%positive.
Definition ___compcert_i64_shr : ident := 63%positive.
Definition ___compcert_i64_smod : ident := 60%positive.
Definition ___compcert_i64_smulh : ident := 65%positive.
Definition ___compcert_i64_stod : ident := 54%positive.
Definition ___compcert_i64_stof : ident := 56%positive.
Definition ___compcert_i64_udiv : ident := 59%positive.
Definition ___compcert_i64_umod : ident := 61%positive.
Definition ___compcert_i64_umulh : ident := 66%positive.
Definition ___compcert_i64_utod : ident := 55%positive.
Definition ___compcert_i64_utof : ident := 57%positive.
Definition ___compcert_va_composite : ident := 51%positive.
Definition ___compcert_va_float64 : ident := 50%positive.
Definition ___compcert_va_int32 : ident := 48%positive.
Definition ___compcert_va_int64 : ident := 49%positive.
Definition ___stringlit_1 : ident := 101%positive.
Definition ___stringlit_2 : ident := 102%positive.
Definition ___stringlit_3 : ident := 103%positive.
Definition _addQueue : ident := 172%positive.
Definition _ai : ident := 203%positive.
Definition _an : ident := 122%positive.
Definition _bi : ident := 204%positive.
Definition _bn : ident := 123%positive.
Definition _chunk : ident := 85%positive.
Definition _chunkA : ident := 133%positive.
Definition _chunkB : ident := 134%positive.
Definition _chunkLen : ident := 137%positive.
Definition _chunkLen__1 : ident := 138%positive.
Definition _chunks : ident := 159%positive.
Definition _cnt : ident := 88%positive.
Definition _col : ident := 6%positive.
Definition _colHead : ident := 106%positive.
Definition _cols : ident := 10%positive.
Definition _comp : ident := 118%positive.
Definition _condense : ident := 168%positive.
Definition _count : ident := 20%positive.
Definition _csr : ident := 97%positive.
Definition _currA : ident := 143%positive.
Definition _currB : ident := 144%positive.
Definition _currComp : ident := 128%positive.
Definition _currLen : ident := 160%positive.
Definition _direction : ident := 141%positive.
Definition _elimZero : ident := 130%positive.
Definition _flattenByMergeTree : ident := 163%positive.
Definition _free : ident := 80%positive.
Definition _gemm_sparch : ident := 201%positive.
Definition _head : ident := 17%positive.
Definition _heap : ident := 22%positive.
Definition _height : ident := 1%positive.
Definition _i : ident := 90%positive.
Definition _i__1 : ident := 110%positive.
Definition _i__2 : ident := 139%positive.
Definition _i__3 : ident := 151%positive.
Definition _i__4 : ident := 198%positive.
Definition _idx : ident := 167%positive.
Definition _index : ident := 180%positive.
Definition _item : ident := 13%positive.
Definition _items : ident := 147%positive.
Definition _iterLen : ident := 202%positive.
Definition _j : ident := 124%positive.
Definition _j__1 : ident := 125%positive.
Definition _j__2 : ident := 140%positive.
Definition _k : ident := 205%positive.
Definition _kInit : ident := 195%positive.
Definition _lastDir : ident := 142%positive.
Definition _lastDirection : ident := 132%positive.
Definition _left : ident := 94%positive.
Definition _leftChunk : ident := 191%positive.
Definition _leftIdx : ident := 173%positive.
Definition _leftLen : ident := 190%positive.
Definition _leftVal : ident := 107%positive.
Definition _len : ident := 16%positive.
Definition _lenA : ident := 120%positive.
Definition _lenB : ident := 121%positive.
Definition _lenLeft : ident := 135%positive.
Definition _lenRight : ident := 136%positive.
Definition _lenVal : ident := 9%positive.
Definition _li : ident := 153%positive.
Definition _litem : ident := 155%positive.
Definition _main : ident := 207%positive.
Definition _malloc : ident := 79%positive.
Definition _mat : ident := 184%positive.
Definition _matA : ident := 188%positive.
Definition _matB : ident := 189%positive.
Definition _matmul : ident := 206%positive.
Definition _matrix : ident := 177%positive.
Definition _maxBound : ident := 117%positive.
Definition _maxChunk : ident := 145%positive.
Definition _maxCount : ident := 21%positive.
Definition _merge : ident := 158%positive.
Definition _mergeHier : ident := 152%positive.
Definition _mergeLow : ident := 131%positive.
Definition _mergeTop : ident := 146%positive.
Definition _mergedIdx : ident := 194%positive.
Definition _mergedVal : ident := 197%positive.
Definition _merger : ident := 161%positive.
Definition _minBound : ident := 116%positive.
Definition _mm : ident := 200%positive.
Definition _multVal : ident := 192%positive.
Definition _newItem : ident := 112%positive.
Definition _next : ident := 15%positive.
Definition _nextLen : ident := 162%positive.
Definition _node : ident := 81%positive.
Definition _offset : ident := 181%positive.
Definition _outLen : ident := 164%positive.
Definition _outerProd : ident := 114%positive.
Definition _parent : ident := 171%positive.
Definition _popQueue : ident := 175%positive.
Definition _posCmp : ident := 115%positive.
Definition _posX : ident := 126%positive.
Definition _posY : ident := 127%positive.
Definition _pq : ident := 193%positive.
Definition _printf : ident := 78%positive.
Definition _queue : ident := 170%positive.
Definition _result : ident := 105%positive.
Definition _ri : ident := 154%positive.
Definition _right : ident := 95%positive.
Definition _rightIdx : ident := 174%positive.
Definition _rightRowEnd : ident := 109%positive.
Definition _rightRowStart : ident := 108%positive.
Definition _rightVal : ident := 111%positive.
Definition _ritem : ident := 156%positive.
Definition _row : ident := 5%positive.
Definition _rowCnt : ident := 165%positive.
Definition _rowCnt__1 : ident := 166%positive.
Definition _rowEnd : ident := 186%positive.
Definition _rowId : ident := 98%positive.
Definition _rowStart : ident := 185%positive.
Definition _rows : ident := 11%positive.
Definition _shift : ident := 148%positive.
Definition _shouldShift : ident := 150%positive.
Definition _spgemm_sparch : ident := 199%positive.
Definition _swapHeap : ident := 169%positive.
Definition _tail : ident := 18%positive.
Definition _tailItem : ident := 157%positive.
Definition _temp : ident := 119%positive.
Definition _tempLen : ident := 129%positive.
Definition _treeItems : ident := 196%positive.
Definition _value : ident := 7%positive.
Definition _values : ident := 3%positive.
Definition _width : ident := 2%positive.
Definition _zeroes : ident := 149%positive.
Definition _t'1 : ident := 208%positive.
Definition _t'10 : ident := 217%positive.
Definition _t'11 : ident := 218%positive.
Definition _t'12 : ident := 219%positive.
Definition _t'13 : ident := 220%positive.
Definition _t'14 : ident := 221%positive.
Definition _t'15 : ident := 222%positive.
Definition _t'16 : ident := 223%positive.
Definition _t'17 : ident := 224%positive.
Definition _t'18 : ident := 225%positive.
Definition _t'19 : ident := 226%positive.
Definition _t'2 : ident := 209%positive.
Definition _t'20 : ident := 227%positive.
Definition _t'21 : ident := 228%positive.
Definition _t'22 : ident := 229%positive.
Definition _t'23 : ident := 230%positive.
Definition _t'24 : ident := 231%positive.
Definition _t'25 : ident := 232%positive.
Definition _t'26 : ident := 233%positive.
Definition _t'27 : ident := 234%positive.
Definition _t'28 : ident := 235%positive.
Definition _t'29 : ident := 236%positive.
Definition _t'3 : ident := 210%positive.
Definition _t'30 : ident := 237%positive.
Definition _t'31 : ident := 238%positive.
Definition _t'32 : ident := 239%positive.
Definition _t'33 : ident := 240%positive.
Definition _t'34 : ident := 241%positive.
Definition _t'35 : ident := 242%positive.
Definition _t'36 : ident := 243%positive.
Definition _t'37 : ident := 244%positive.
Definition _t'38 : ident := 245%positive.
Definition _t'39 : ident := 246%positive.
Definition _t'4 : ident := 211%positive.
Definition _t'40 : ident := 247%positive.
Definition _t'41 : ident := 248%positive.
Definition _t'5 : ident := 212%positive.
Definition _t'6 : ident := 213%positive.
Definition _t'7 : ident := 214%positive.
Definition _t'8 : ident := 215%positive.
Definition _t'9 : ident := 216%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 77) ::
                Init_int8 (Int.repr 80) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 89) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 19);
  gvar_init := (Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 44) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 11);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_LLNode_malloc := {|
  fn_return := (tptr (Tstruct __LLNode noattr));
  fn_callconv := cc_default;
  fn_params := ((_item, (tptr (Tstruct __COOItem noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_node, (tptr (Tstruct __LLNode noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct __LLNode noattr) tuint) :: nil))
    (Sset _node
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct __LLNode noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _node (tptr (Tstruct __LLNode noattr)))
          (Tstruct __LLNode noattr)) _item (tptr (Tstruct __COOItem noattr)))
      (Etempvar _item (tptr (Tstruct __COOItem noattr))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _node (tptr (Tstruct __LLNode noattr)))
            (Tstruct __LLNode noattr)) _next
          (tptr (Tstruct __LLNode noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Sreturn (Some (Etempvar _node (tptr (Tstruct __LLNode noattr))))))))
|}.

Definition f_LLNode_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_node, (tptr (Tstruct __LLNode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
  ((Etempvar _node (tptr (Tstruct __LLNode noattr))) :: nil))
|}.

Definition f_LLNode_freeAll := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_node, (tptr (Tstruct __LLNode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct __COOItem noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _node (tptr (Tstruct __LLNode noattr)))
          (Tstruct __LLNode noattr)) _item (tptr (Tstruct __COOItem noattr))))
    (Scall None
      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _t'1 (tptr (Tstruct __COOItem noattr))) :: nil)))
  (Scall None
    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
    ((Etempvar _node (tptr (Tstruct __LLNode noattr))) :: nil)))
|}.

Definition f_COOChunk_malloc := {|
  fn_return := (tptr (Tstruct __COOChunk noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_chunk, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct __COOChunk noattr) tuint) :: nil))
    (Sset _chunk
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct __COOChunk noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
          (Tstruct __COOChunk noattr)) _len tuint)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
            (Tstruct __COOChunk noattr)) _head
          (tptr (Tstruct __LLNode noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _tail
            (tptr (Tstruct __LLNode noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Sreturn (Some (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))))))))
|}.

Definition f_COOChunk_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_chunk, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
  ((Etempvar _chunk (tptr (Tstruct __COOChunk noattr))) :: nil))
|}.

Definition f_COOChunk_freeNodes := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_chunk, (tptr (Tstruct __COOChunk noattr))) ::
                (_cnt, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_next, (tptr (Tstruct __LLNode noattr))) :: (_t'1, tint) ::
               (_t'6, tuint) :: (_t'5, (tptr (Tstruct __LLNode noattr))) ::
               (_t'4, (tptr (Tstruct __LLNode noattr))) :: (_t'3, tuint) ::
               (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sloop
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'6
            (Efield
              (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
                (Tstruct __COOChunk noattr)) _len tuint))
          (Sifthenelse (Ebinop Ogt (Etempvar _t'6 tuint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sset _t'1
              (Ecast
                (Ebinop Ogt (Etempvar _cnt tuint)
                  (Econst_int (Int.repr 0) tint) tint) tbool))
            (Sset _t'1 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
                (Tstruct __COOChunk noattr)) _head
              (tptr (Tstruct __LLNode noattr))))
          (Sset _next
            (Efield
              (Ederef (Etempvar _t'5 (tptr (Tstruct __LLNode noattr)))
                (Tstruct __LLNode noattr)) _next
              (tptr (Tstruct __LLNode noattr)))))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
                  (Tstruct __COOChunk noattr)) _head
                (tptr (Tstruct __LLNode noattr))))
            (Scall None
              (Evar _LLNode_freeAll (Tfunction
                                      (Tcons (tptr (Tstruct __LLNode noattr))
                                        Tnil) tvoid cc_default))
              ((Etempvar _t'4 (tptr (Tstruct __LLNode noattr))) :: nil)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
                  (Tstruct __COOChunk noattr)) _head
                (tptr (Tstruct __LLNode noattr)))
              (Etempvar _next (tptr (Tstruct __LLNode noattr))))
            (Ssequence
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef
                      (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
                      (Tstruct __COOChunk noattr)) _len tuint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
                      (Tstruct __COOChunk noattr)) _len tuint)
                  (Ebinop Osub (Etempvar _t'3 tuint)
                    (Econst_int (Int.repr 1) tint) tuint)))
              (Sset _cnt
                (Ebinop Osub (Etempvar _cnt tuint)
                  (Econst_int (Int.repr 1) tint) tuint)))))))
    Sskip)
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
          (Tstruct __COOChunk noattr)) _len tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _head
            (tptr (Tstruct __LLNode noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Sassign
          (Efield
            (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _tail
            (tptr (Tstruct __LLNode noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
      Sskip)))
|}.

Definition f_COOChunk_freeAll := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_chunk, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_head, (tptr (Tstruct __LLNode noattr))) ::
               (_next, (tptr (Tstruct __LLNode noattr))) :: (_len, tuint) ::
               (_i, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _len
    (Efield
      (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
        (Tstruct __COOChunk noattr)) _len tuint))
  (Ssequence
    (Sset _head
      (Efield
        (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
          (Tstruct __COOChunk noattr)) _head
        (tptr (Tstruct __LLNode noattr))))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                           (Etempvar _len tuint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _next
                (Efield
                  (Ederef (Etempvar _head (tptr (Tstruct __LLNode noattr)))
                    (Tstruct __LLNode noattr)) _next
                  (tptr (Tstruct __LLNode noattr))))
              (Ssequence
                (Scall None
                  (Evar _LLNode_freeAll (Tfunction
                                          (Tcons
                                            (tptr (Tstruct __LLNode noattr))
                                            Tnil) tvoid cc_default))
                  ((Etempvar _head (tptr (Tstruct __LLNode noattr))) :: nil))
                (Sset _head
                  (Etempvar _next (tptr (Tstruct __LLNode noattr)))))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint))))
      (Scall None
        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Etempvar _chunk (tptr (Tstruct __COOChunk noattr))) :: nil)))))
|}.

Definition f_COOChunk_push := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_chunk, (tptr (Tstruct __COOChunk noattr))) ::
                (_item, (tptr (Tstruct __COOItem noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_node, (tptr (Tstruct __LLNode noattr))) ::
               (_t'1, (tptr (Tstruct __LLNode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _LLNode_malloc (Tfunction
                             (Tcons (tptr (Tstruct __COOItem noattr)) Tnil)
                             (tptr (Tstruct __LLNode noattr)) cc_default))
      ((Etempvar _item (tptr (Tstruct __COOItem noattr))) :: nil))
    (Sset _node (Etempvar _t'1 (tptr (Tstruct __LLNode noattr)))))
  (Scall None
    (Evar _COOChunk_append (Tfunction
                             (Tcons (tptr (Tstruct __COOChunk noattr))
                               (Tcons (tptr (Tstruct __LLNode noattr)) Tnil))
                             tvoid cc_default))
    ((Etempvar _chunk (tptr (Tstruct __COOChunk noattr))) ::
     (Etempvar _node (tptr (Tstruct __LLNode noattr))) :: nil)))
|}.

Definition f_COOChunk_append := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_chunk, (tptr (Tstruct __COOChunk noattr))) ::
                (_node, (tptr (Tstruct __LLNode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, (tptr (Tstruct __LLNode noattr))) ::
               (_t'2, (tptr (Tstruct __LLNode noattr))) :: (_t'1, tuint) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
          (Tstruct __COOChunk noattr)) _tail
        (tptr (Tstruct __LLNode noattr))))
    (Sifthenelse (Etempvar _t'2 (tptr (Tstruct __LLNode noattr)))
      (Ssequence
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
                (Tstruct __COOChunk noattr)) _tail
              (tptr (Tstruct __LLNode noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _t'3 (tptr (Tstruct __LLNode noattr)))
                (Tstruct __LLNode noattr)) _next
              (tptr (Tstruct __LLNode noattr)))
            (Etempvar _node (tptr (Tstruct __LLNode noattr)))))
        (Sassign
          (Efield
            (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _tail
            (tptr (Tstruct __LLNode noattr)))
          (Etempvar _node (tptr (Tstruct __LLNode noattr)))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _tail
            (tptr (Tstruct __LLNode noattr)))
          (Etempvar _node (tptr (Tstruct __LLNode noattr))))
        (Sassign
          (Efield
            (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _head
            (tptr (Tstruct __LLNode noattr)))
          (Etempvar _node (tptr (Tstruct __LLNode noattr)))))))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
          (Tstruct __COOChunk noattr)) _len tuint))
    (Sassign
      (Efield
        (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
          (Tstruct __COOChunk noattr)) _len tuint)
      (Ebinop Oadd (Etempvar _t'1 tuint) (Econst_int (Int.repr 1) tint)
        tuint))))
|}.

Definition f_COOChunk_concat := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_left, (tptr (Tstruct __COOChunk noattr))) ::
                (_right, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'10, tuint) :: (_t'9, tuint) ::
               (_t'8, (tptr (Tstruct __LLNode noattr))) ::
               (_t'7, (tptr (Tstruct __LLNode noattr))) ::
               (_t'6, (tptr (Tstruct __LLNode noattr))) ::
               (_t'5, (tptr (Tstruct __LLNode noattr))) :: (_t'4, tuint) ::
               (_t'3, (tptr (Tstruct __LLNode noattr))) ::
               (_t'2, (tptr (Tstruct __LLNode noattr))) ::
               (_t'1, (tptr (Tstruct __LLNode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
        (Tstruct __COOChunk noattr)) _tail (tptr (Tstruct __LLNode noattr))))
  (Sifthenelse (Etempvar _t'1 (tptr (Tstruct __LLNode noattr)))
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
            (Tstruct __COOChunk noattr)) _tail
          (tptr (Tstruct __LLNode noattr))))
      (Sifthenelse (Etempvar _t'5 (tptr (Tstruct __LLNode noattr)))
        (Ssequence
          (Ssequence
            (Sset _t'9
              (Efield
                (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                  (Tstruct __COOChunk noattr)) _len tuint))
            (Ssequence
              (Sset _t'10
                (Efield
                  (Ederef
                    (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                    (Tstruct __COOChunk noattr)) _len tuint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                    (Tstruct __COOChunk noattr)) _len tuint)
                (Ebinop Oadd (Etempvar _t'9 tuint) (Etempvar _t'10 tuint)
                  tuint))))
          (Ssequence
            (Ssequence
              (Sset _t'7
                (Efield
                  (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                    (Tstruct __COOChunk noattr)) _tail
                  (tptr (Tstruct __LLNode noattr))))
              (Ssequence
                (Sset _t'8
                  (Efield
                    (Ederef
                      (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                      (Tstruct __COOChunk noattr)) _head
                    (tptr (Tstruct __LLNode noattr))))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _t'7 (tptr (Tstruct __LLNode noattr)))
                      (Tstruct __LLNode noattr)) _next
                    (tptr (Tstruct __LLNode noattr)))
                  (Etempvar _t'8 (tptr (Tstruct __LLNode noattr))))))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef
                    (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                    (Tstruct __COOChunk noattr)) _tail
                  (tptr (Tstruct __LLNode noattr))))
              (Sassign
                (Efield
                  (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                    (Tstruct __COOChunk noattr)) _tail
                  (tptr (Tstruct __LLNode noattr)))
                (Etempvar _t'6 (tptr (Tstruct __LLNode noattr)))))))
        Sskip))
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _len tuint))
        (Sassign
          (Efield
            (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _len tuint) (Etempvar _t'4 tuint)))
      (Ssequence
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                (Tstruct __COOChunk noattr)) _head
              (tptr (Tstruct __LLNode noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                (Tstruct __COOChunk noattr)) _head
              (tptr (Tstruct __LLNode noattr)))
            (Etempvar _t'3 (tptr (Tstruct __LLNode noattr)))))
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                (Tstruct __COOChunk noattr)) _tail
              (tptr (Tstruct __LLNode noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                (Tstruct __COOChunk noattr)) _tail
              (tptr (Tstruct __LLNode noattr)))
            (Etempvar _t'2 (tptr (Tstruct __LLNode noattr)))))))))
|}.

Definition f_COOChunk_toCSR := {|
  fn_return := (tptr (Tstruct __CSRMatrix noattr));
  fn_callconv := cc_default;
  fn_params := ((_chunk, (tptr (Tstruct __COOChunk noattr))) ::
                (_height, tuint) :: (_width, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_len, tuint) ::
               (_csr, (tptr (Tstruct __CSRMatrix noattr))) ::
               (_head, (tptr (Tstruct __LLNode noattr))) ::
               (_item, (tptr (Tstruct __COOItem noattr))) ::
               (_rowId, tuint) :: (_i, tuint) ::
               (_t'1, (tptr (Tstruct __CSRMatrix noattr))) ::
               (_t'9, (tptr tuint)) :: (_t'8, tfloat) ::
               (_t'7, (tptr tfloat)) :: (_t'6, tuint) ::
               (_t'5, (tptr tuint)) :: (_t'4, tuint) ::
               (_t'3, (tptr tuint)) :: (_t'2, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _len
    (Efield
      (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
        (Tstruct __COOChunk noattr)) _len tuint))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _CSR_malloc (Tfunction
                            (Tcons tuint (Tcons tuint (Tcons tuint Tnil)))
                            (tptr (Tstruct __CSRMatrix noattr)) cc_default))
        ((Etempvar _height tuint) :: (Etempvar _width tuint) ::
         (Etempvar _len tuint) :: nil))
      (Sset _csr (Etempvar _t'1 (tptr (Tstruct __CSRMatrix noattr)))))
    (Ssequence
      (Sset _head
        (Efield
          (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
            (Tstruct __COOChunk noattr)) _head
          (tptr (Tstruct __LLNode noattr))))
      (Ssequence
        (Sset _rowId (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Ssequence
            (Sset _t'9
              (Efield
                (Ederef (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                  (Tstruct __CSRMatrix noattr)) _rows (tptr tuint)))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _t'9 (tptr tuint))
                  (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
              (Econst_int (Int.repr 0) tint)))
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                 (Etempvar _len tuint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _item
                      (Efield
                        (Ederef
                          (Etempvar _head (tptr (Tstruct __LLNode noattr)))
                          (Tstruct __LLNode noattr)) _item
                        (tptr (Tstruct __COOItem noattr))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'7
                          (Efield
                            (Ederef
                              (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                              (Tstruct __CSRMatrix noattr)) _values
                            (tptr tfloat)))
                        (Ssequence
                          (Sset _t'8
                            (Efield
                              (Ederef
                                (Etempvar _item (tptr (Tstruct __COOItem noattr)))
                                (Tstruct __COOItem noattr)) _value tfloat))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Etempvar _t'7 (tptr tfloat))
                                (Etempvar _i tuint) (tptr tfloat)) tfloat)
                            (Etempvar _t'8 tfloat))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'5
                            (Efield
                              (Ederef
                                (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                (Tstruct __CSRMatrix noattr)) _cols
                              (tptr tuint)))
                          (Ssequence
                            (Sset _t'6
                              (Efield
                                (Ederef
                                  (Etempvar _item (tptr (Tstruct __COOItem noattr)))
                                  (Tstruct __COOItem noattr)) _col tuint))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _t'5 (tptr tuint))
                                  (Etempvar _i tuint) (tptr tuint)) tuint)
                              (Etempvar _t'6 tuint))))
                        (Ssequence
                          (Sloop
                            (Ssequence
                              (Ssequence
                                (Sset _t'4
                                  (Efield
                                    (Ederef
                                      (Etempvar _item (tptr (Tstruct __COOItem noattr)))
                                      (Tstruct __COOItem noattr)) _row tuint))
                                (Sifthenelse (Ebinop Olt
                                               (Etempvar _rowId tuint)
                                               (Etempvar _t'4 tuint) tint)
                                  Sskip
                                  Sbreak))
                              (Ssequence
                                (Sset _rowId
                                  (Ebinop Oadd (Etempvar _rowId tuint)
                                    (Econst_int (Int.repr 1) tint) tuint))
                                (Ssequence
                                  (Sset _t'3
                                    (Efield
                                      (Ederef
                                        (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                        (Tstruct __CSRMatrix noattr)) _rows
                                      (tptr tuint)))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _t'3 (tptr tuint))
                                        (Etempvar _rowId tuint) (tptr tuint))
                                      tuint) (Etempvar _i tuint)))))
                            Sskip)
                          (Sset _head
                            (Efield
                              (Ederef
                                (Etempvar _head (tptr (Tstruct __LLNode noattr)))
                                (Tstruct __LLNode noattr)) _next
                              (tptr (Tstruct __LLNode noattr)))))))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tuint)
                    (Econst_int (Int.repr 1) tint) tuint))))
            (Ssequence
              (Swhile
                (Ebinop Olt (Etempvar _rowId tuint) (Etempvar _height tuint)
                  tint)
                (Ssequence
                  (Sset _rowId
                    (Ebinop Oadd (Etempvar _rowId tuint)
                      (Econst_int (Int.repr 1) tint) tuint))
                  (Ssequence
                    (Sset _t'2
                      (Efield
                        (Ederef
                          (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                          (Tstruct __CSRMatrix noattr)) _rows (tptr tuint)))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _t'2 (tptr tuint))
                          (Etempvar _rowId tuint) (tptr tuint)) tuint)
                      (Etempvar _len tuint)))))
              (Sreturn (Some (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr))))))))))))
|}.

Definition f_COOChunk_print := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_chunk, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_node, (tptr (Tstruct __LLNode noattr))) :: (_t'7, tuint) ::
               (_t'6, tfloat) :: (_t'5, (tptr (Tstruct __COOItem noattr))) ::
               (_t'4, tuint) :: (_t'3, (tptr (Tstruct __COOItem noattr))) ::
               (_t'2, tuint) :: (_t'1, (tptr (Tstruct __COOItem noattr))) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _node
    (Efield
      (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
        (Tstruct __COOChunk noattr)) _head (tptr (Tstruct __LLNode noattr))))
  (Sifthenelse (Etempvar _node (tptr (Tstruct __LLNode noattr)))
    (Ssequence
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _len tuint))
        (Scall None
          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                          {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
          ((Evar ___stringlit_2 (tarray tschar 11)) ::
           (Etempvar _t'7 tuint) :: nil)))
      (Swhile
        (Etempvar _node (tptr (Tstruct __LLNode noattr)))
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef (Etempvar _node (tptr (Tstruct __LLNode noattr)))
                  (Tstruct __LLNode noattr)) _item
                (tptr (Tstruct __COOItem noattr))))
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef (Etempvar _t'1 (tptr (Tstruct __COOItem noattr)))
                    (Tstruct __COOItem noattr)) _row tuint))
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef (Etempvar _node (tptr (Tstruct __LLNode noattr)))
                      (Tstruct __LLNode noattr)) _item
                    (tptr (Tstruct __COOItem noattr))))
                (Ssequence
                  (Sset _t'4
                    (Efield
                      (Ederef
                        (Etempvar _t'3 (tptr (Tstruct __COOItem noattr)))
                        (Tstruct __COOItem noattr)) _col tuint))
                  (Ssequence
                    (Sset _t'5
                      (Efield
                        (Ederef
                          (Etempvar _node (tptr (Tstruct __LLNode noattr)))
                          (Tstruct __LLNode noattr)) _item
                        (tptr (Tstruct __COOItem noattr))))
                    (Ssequence
                      (Sset _t'6
                        (Efield
                          (Ederef
                            (Etempvar _t'5 (tptr (Tstruct __COOItem noattr)))
                            (Tstruct __COOItem noattr)) _value tfloat))
                      (Scall None
                        (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                        tint
                                        {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                        ((Evar ___stringlit_3 (tarray tschar 19)) ::
                         (Etempvar _t'2 tuint) :: (Etempvar _t'4 tuint) ::
                         (Etempvar _t'6 tfloat) :: nil))))))))
          (Sset _node
            (Efield
              (Ederef (Etempvar _node (tptr (Tstruct __LLNode noattr)))
                (Tstruct __LLNode noattr)) _next
              (tptr (Tstruct __LLNode noattr)))))))
    (Scall None
      (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                      {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
      ((Evar ___stringlit_1 (tarray tschar 7)) :: nil))))
|}.

Definition f_outerProd := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_left, (tptr (Tstruct __COOChunk noattr))) ::
                (_right, (tptr (Tstruct __CSRMatrix noattr))) ::
                (_result, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_len, tuint) ::
               (_colHead, (tptr (Tstruct __LLNode noattr))) :: (_i, tuint) ::
               (_item, (tptr (Tstruct __COOItem noattr))) ::
               (_leftVal, tfloat) :: (_row, tuint) :: (_rowId, tuint) ::
               (_rightRowStart, tuint) :: (_rightRowEnd, tuint) ::
               (_i__1, tuint) :: (_rightVal, tfloat) :: (_col, tuint) ::
               (_newItem, (tptr (Tstruct __COOItem noattr))) ::
               (_t'1, (tptr (Tstruct __COOItem noattr))) ::
               (_t'5, (tptr tuint)) :: (_t'4, (tptr tuint)) ::
               (_t'3, (tptr tfloat)) :: (_t'2, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _len
    (Efield
      (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
        (Tstruct __COOChunk noattr)) _len tuint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
          (Tstruct __COOChunk noattr)) _len tuint)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
            (Tstruct __COOChunk noattr)) _head
          (tptr (Tstruct __LLNode noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _tail
            (tptr (Tstruct __LLNode noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence
          (Sset _colHead
            (Efield
              (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                (Tstruct __COOChunk noattr)) _head
              (tptr (Tstruct __LLNode noattr))))
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                 (Etempvar _len tuint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _item
                      (Efield
                        (Ederef
                          (Etempvar _colHead (tptr (Tstruct __LLNode noattr)))
                          (Tstruct __LLNode noattr)) _item
                        (tptr (Tstruct __COOItem noattr))))
                    (Ssequence
                      (Sset _leftVal
                        (Efield
                          (Ederef
                            (Etempvar _item (tptr (Tstruct __COOItem noattr)))
                            (Tstruct __COOItem noattr)) _value tfloat))
                      (Ssequence
                        (Sset _row
                          (Efield
                            (Ederef
                              (Etempvar _item (tptr (Tstruct __COOItem noattr)))
                              (Tstruct __COOItem noattr)) _row tuint))
                        (Ssequence
                          (Sset _rowId
                            (Efield
                              (Ederef
                                (Etempvar _item (tptr (Tstruct __COOItem noattr)))
                                (Tstruct __COOItem noattr)) _col tuint))
                          (Ssequence
                            (Ssequence
                              (Sset _t'5
                                (Efield
                                  (Ederef
                                    (Etempvar _right (tptr (Tstruct __CSRMatrix noattr)))
                                    (Tstruct __CSRMatrix noattr)) _rows
                                  (tptr tuint)))
                              (Sset _rightRowStart
                                (Ederef
                                  (Ebinop Oadd (Etempvar _t'5 (tptr tuint))
                                    (Etempvar _rowId tuint) (tptr tuint))
                                  tuint)))
                            (Ssequence
                              (Ssequence
                                (Sset _t'4
                                  (Efield
                                    (Ederef
                                      (Etempvar _right (tptr (Tstruct __CSRMatrix noattr)))
                                      (Tstruct __CSRMatrix noattr)) _rows
                                    (tptr tuint)))
                                (Sset _rightRowEnd
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _t'4 (tptr tuint))
                                      (Ebinop Oadd (Etempvar _rowId tuint)
                                        (Econst_int (Int.repr 1) tint) tuint)
                                      (tptr tuint)) tuint)))
                              (Ssequence
                                (Ssequence
                                  (Sset _i__1
                                    (Etempvar _rightRowStart tuint))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _i__1 tuint)
                                                     (Etempvar _rightRowEnd tuint)
                                                     tint)
                                        Sskip
                                        Sbreak)
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'3
                                            (Efield
                                              (Ederef
                                                (Etempvar _right (tptr (Tstruct __CSRMatrix noattr)))
                                                (Tstruct __CSRMatrix noattr))
                                              _values (tptr tfloat)))
                                          (Sset _rightVal
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _t'3 (tptr tfloat))
                                                (Etempvar _i__1 tuint)
                                                (tptr tfloat)) tfloat)))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'2
                                              (Efield
                                                (Ederef
                                                  (Etempvar _right (tptr (Tstruct __CSRMatrix noattr)))
                                                  (Tstruct __CSRMatrix noattr))
                                                _cols (tptr tuint)))
                                            (Sset _col
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _t'2 (tptr tuint))
                                                  (Etempvar _i__1 tuint)
                                                  (tptr tuint)) tuint)))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'1)
                                                (Evar _COOItem_malloc 
                                                (Tfunction
                                                  (Tcons tuint
                                                    (Tcons tuint
                                                      (Tcons tfloat Tnil)))
                                                  (tptr (Tstruct __COOItem noattr))
                                                  cc_default))
                                                ((Etempvar _row tuint) ::
                                                 (Etempvar _col tuint) ::
                                                 (Ebinop Omul
                                                   (Etempvar _leftVal tfloat)
                                                   (Etempvar _rightVal tfloat)
                                                   tfloat) :: nil))
                                              (Sset _newItem
                                                (Etempvar _t'1 (tptr (Tstruct __COOItem noattr)))))
                                            (Scall None
                                              (Evar _COOChunk_push (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOItem noattr))
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                              ((Etempvar _result (tptr (Tstruct __COOChunk noattr))) ::
                                               (Etempvar _newItem (tptr (Tstruct __COOItem noattr))) ::
                                               nil))))))
                                    (Sset _i__1
                                      (Ebinop Oadd (Etempvar _i__1 tuint)
                                        (Econst_int (Int.repr 1) tint) tuint))))
                                (Sset _colHead
                                  (Efield
                                    (Ederef
                                      (Etempvar _colHead (tptr (Tstruct __LLNode noattr)))
                                      (Tstruct __LLNode noattr)) _next
                                    (tptr (Tstruct __LLNode noattr))))))))))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tuint)
                    (Econst_int (Int.repr 1) tint) tuint))))
            (Sreturn None)))))))
|}.

Definition f_posCmp := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_left, (tptr (Tstruct __COOItem noattr))) ::
                (_right, (tptr (Tstruct __COOItem noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'8, tuint) :: (_t'7, tuint) :: (_t'6, tuint) ::
               (_t'5, tuint) :: (_t'4, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _left (tptr (Tstruct __COOItem noattr)))
        (Tstruct __COOItem noattr)) _row tuint))
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _right (tptr (Tstruct __COOItem noattr)))
          (Tstruct __COOItem noattr)) _row tuint))
    (Sifthenelse (Ebinop Olt (Etempvar _t'1 tuint) (Etempvar _t'2 tuint)
                   tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _left (tptr (Tstruct __COOItem noattr)))
              (Tstruct __COOItem noattr)) _row tuint))
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _right (tptr (Tstruct __COOItem noattr)))
                (Tstruct __COOItem noattr)) _row tuint))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tuint)
                         (Etempvar _t'4 tuint) tint)
            (Ssequence
              (Sset _t'5
                (Efield
                  (Ederef (Etempvar _left (tptr (Tstruct __COOItem noattr)))
                    (Tstruct __COOItem noattr)) _col tuint))
              (Ssequence
                (Sset _t'6
                  (Efield
                    (Ederef
                      (Etempvar _right (tptr (Tstruct __COOItem noattr)))
                      (Tstruct __COOItem noattr)) _col tuint))
                (Sifthenelse (Ebinop Olt (Etempvar _t'5 tuint)
                               (Etempvar _t'6 tuint) tint)
                  (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                   tint)))
                  (Ssequence
                    (Sset _t'7
                      (Efield
                        (Ederef
                          (Etempvar _left (tptr (Tstruct __COOItem noattr)))
                          (Tstruct __COOItem noattr)) _col tuint))
                    (Ssequence
                      (Sset _t'8
                        (Efield
                          (Ederef
                            (Etempvar _right (tptr (Tstruct __COOItem noattr)))
                            (Tstruct __COOItem noattr)) _col tuint))
                      (Sifthenelse (Ebinop Oeq (Etempvar _t'7 tuint)
                                     (Etempvar _t'8 tuint) tint)
                        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                        (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))))
            (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))))
|}.

Definition f_mergeLow := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_left, (tptr (Tstruct __COOChunk noattr))) ::
                (_right, (tptr (Tstruct __COOChunk noattr))) ::
                (_minBound, (tptr (Tstruct __COOItem noattr))) ::
                (_maxBound, (tptr (Tstruct __COOItem noattr))) ::
                (_result, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_vars := ((_comp, (tarray (tarray tint 5) 5)) ::
              (_temp, (Tstruct __COOChunk noattr)) :: nil);
  fn_temps := ((_lenA, tuint) :: (_lenB, tuint) ::
               (_an, (tptr (Tstruct __LLNode noattr))) ::
               (_bn, (tptr (Tstruct __LLNode noattr))) :: (_i, tuint) ::
               (_j, tuint) :: (_j__1, tuint) :: (_posX, tuint) ::
               (_posY, tuint) :: (_currComp, tint) ::
               (_item, (tptr (Tstruct __COOItem noattr))) ::
               (_tempLen, tuint) :: (_i__1, tuint) :: (_t'10, tint) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, tint) ::
               (_t'6, tint) :: (_t'5, (tptr (Tstruct __COOItem noattr))) ::
               (_t'4, (tptr (Tstruct __COOItem noattr))) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) ::
               (_t'39, (tptr (Tstruct __COOItem noattr))) ::
               (_t'38, (tptr (Tstruct __COOItem noattr))) ::
               (_t'37, tfloat) ::
               (_t'36, (tptr (Tstruct __COOItem noattr))) ::
               (_t'35, tuint) ::
               (_t'34, (tptr (Tstruct __COOItem noattr))) ::
               (_t'33, tuint) ::
               (_t'32, (tptr (Tstruct __COOItem noattr))) ::
               (_t'31, tfloat) ::
               (_t'30, (tptr (Tstruct __COOItem noattr))) ::
               (_t'29, tuint) ::
               (_t'28, (tptr (Tstruct __COOItem noattr))) ::
               (_t'27, tuint) ::
               (_t'26, (tptr (Tstruct __COOItem noattr))) ::
               (_t'25, (tptr (Tstruct __COOItem noattr))) ::
               (_t'24, (tptr (Tstruct __LLNode noattr))) ::
               (_t'23, (tptr (Tstruct __COOItem noattr))) ::
               (_t'22, (tptr (Tstruct __LLNode noattr))) ::
               (_t'21, tfloat) ::
               (_t'20, (tptr (Tstruct __COOItem noattr))) ::
               (_t'19, (tptr (Tstruct __LLNode noattr))) ::
               (_t'18, tfloat) ::
               (_t'17, (tptr (Tstruct __COOItem noattr))) ::
               (_t'16, (tptr (Tstruct __COOItem noattr))) ::
               (_t'15, (tptr (Tstruct __COOItem noattr))) ::
               (_t'14, (tptr (Tstruct __LLNode noattr))) ::
               (_t'13, (tptr (Tstruct __COOItem noattr))) ::
               (_t'12, (tptr (Tstruct __COOItem noattr))) ::
               (_t'11, (tptr (Tstruct __COOItem noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Efield (Evar _temp (Tstruct __COOChunk noattr)) _len tuint)
    (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sassign
      (Efield (Evar _temp (Tstruct __COOChunk noattr)) _head
        (tptr (Tstruct __LLNode noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Sassign
        (Efield (Evar _temp (Tstruct __COOChunk noattr)) _tail
          (tptr (Tstruct __LLNode noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Ssequence
        (Sset _lenA
          (Efield
            (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _len tuint))
        (Ssequence
          (Sset _lenB
            (Efield
              (Ederef (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                (Tstruct __COOChunk noattr)) _len tuint))
          (Ssequence
            (Sset _bn
              (Efield
                (Ederef (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                  (Tstruct __COOChunk noattr)) _head
                (tptr (Tstruct __LLNode noattr))))
            (Ssequence
              (Ssequence
                (Sset _i (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                   (Etempvar _lenB tuint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sset _an
                        (Efield
                          (Ederef
                            (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                            (Tstruct __COOChunk noattr)) _head
                          (tptr (Tstruct __LLNode noattr))))
                      (Ssequence
                        (Ssequence
                          (Sset _j (Econst_int (Int.repr 0) tint))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Olt (Etempvar _j tuint)
                                             (Etempvar _lenA tuint) tint)
                                Sskip
                                Sbreak)
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'38
                                        (Efield
                                          (Ederef
                                            (Etempvar _an (tptr (Tstruct __LLNode noattr)))
                                            (Tstruct __LLNode noattr)) _item
                                          (tptr (Tstruct __COOItem noattr))))
                                      (Ssequence
                                        (Sset _t'39
                                          (Efield
                                            (Ederef
                                              (Etempvar _bn (tptr (Tstruct __LLNode noattr)))
                                              (Tstruct __LLNode noattr))
                                            _item
                                            (tptr (Tstruct __COOItem noattr))))
                                        (Scall (Some _t'1)
                                          (Evar _posCmp (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct __COOItem noattr))
                                                            (Tcons
                                                              (tptr (Tstruct __COOItem noattr))
                                                              Tnil)) tint
                                                          cc_default))
                                          ((Etempvar _t'38 (tptr (Tstruct __COOItem noattr))) ::
                                           (Etempvar _t'39 (tptr (Tstruct __COOItem noattr))) ::
                                           nil))))
                                    (Sifthenelse (Ebinop Ogt
                                                   (Etempvar _t'1 tint)
                                                   (Econst_int (Int.repr 0) tint)
                                                   tint)
                                      (Sset _t'2
                                        (Ecast (Econst_int (Int.repr 1) tint)
                                          tint))
                                      (Sset _t'2
                                        (Ecast (Econst_int (Int.repr 0) tint)
                                          tint))))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _comp (tarray (tarray tint 5) 5))
                                            (Etempvar _i tuint)
                                            (tptr (tarray tint 5)))
                                          (tarray tint 5))
                                        (Etempvar _j tuint) (tptr tint))
                                      tint) (Etempvar _t'2 tint)))
                                (Sset _an
                                  (Efield
                                    (Ederef
                                      (Etempvar _an (tptr (Tstruct __LLNode noattr)))
                                      (Tstruct __LLNode noattr)) _next
                                    (tptr (Tstruct __LLNode noattr))))))
                            (Sset _j
                              (Ebinop Oadd (Etempvar _j tuint)
                                (Econst_int (Int.repr 1) tint) tuint))))
                        (Ssequence
                          (Sset _bn
                            (Efield
                              (Ederef
                                (Etempvar _bn (tptr (Tstruct __LLNode noattr)))
                                (Tstruct __LLNode noattr)) _next
                              (tptr (Tstruct __LLNode noattr))))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar _comp (tarray (tarray tint 5) 5))
                                    (Etempvar _i tuint)
                                    (tptr (tarray tint 5))) (tarray tint 5))
                                (Etempvar _lenA tuint) (tptr tint)) tint)
                            (Econst_int (Int.repr 1) tint))))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tuint)
                      (Econst_int (Int.repr 1) tint) tuint))))
              (Ssequence
                (Ssequence
                  (Sset _j__1 (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Ole (Etempvar _j__1 tuint)
                                     (Etempvar _lenA tuint) tint)
                        Sskip
                        Sbreak)
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Ederef
                              (Ebinop Oadd
                                (Evar _comp (tarray (tarray tint 5) 5))
                                (Etempvar _lenB tuint)
                                (tptr (tarray tint 5))) (tarray tint 5))
                            (Etempvar _j__1 tuint) (tptr tint)) tint)
                        (Econst_int (Int.repr 0) tint)))
                    (Sset _j__1
                      (Ebinop Oadd (Etempvar _j__1 tuint)
                        (Econst_int (Int.repr 1) tint) tuint))))
                (Ssequence
                  (Sset _posX (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sset _posY (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Sset _an
                        (Efield
                          (Ederef
                            (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                            (Tstruct __COOChunk noattr)) _head
                          (tptr (Tstruct __LLNode noattr))))
                      (Ssequence
                        (Sset _bn
                          (Efield
                            (Ederef
                              (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                              (Tstruct __COOChunk noattr)) _head
                            (tptr (Tstruct __LLNode noattr))))
                        (Ssequence
                          (Sloop
                            (Ssequence
                              (Ssequence
                                (Sifthenelse (Ebinop Oge
                                               (Etempvar _posX tuint)
                                               (Etempvar _lenA tuint) tint)
                                  (Sset _t'3
                                    (Ecast
                                      (Ebinop Oge (Etempvar _posY tuint)
                                        (Etempvar _lenB tuint) tint) tbool))
                                  (Sset _t'3 (Econst_int (Int.repr 0) tint)))
                                (Sifthenelse (Eunop Onotbool
                                               (Etempvar _t'3 tint) tint)
                                  Sskip
                                  Sbreak))
                              (Ssequence
                                (Sset _currComp
                                  (Ederef
                                    (Ebinop Oadd
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _comp (tarray (tarray tint 5) 5))
                                          (Etempvar _posY tuint)
                                          (tptr (tarray tint 5)))
                                        (tarray tint 5))
                                      (Etempvar _posX tuint) (tptr tint))
                                    tint))
                                (Ssequence
                                  (Sifthenelse (Etempvar _currComp tint)
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'32
                                            (Efield
                                              (Ederef
                                                (Etempvar _bn (tptr (Tstruct __LLNode noattr)))
                                                (Tstruct __LLNode noattr))
                                              _item
                                              (tptr (Tstruct __COOItem noattr))))
                                          (Ssequence
                                            (Sset _t'33
                                              (Efield
                                                (Ederef
                                                  (Etempvar _t'32 (tptr (Tstruct __COOItem noattr)))
                                                  (Tstruct __COOItem noattr))
                                                _row tuint))
                                            (Ssequence
                                              (Sset _t'34
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _bn (tptr (Tstruct __LLNode noattr)))
                                                    (Tstruct __LLNode noattr))
                                                  _item
                                                  (tptr (Tstruct __COOItem noattr))))
                                              (Ssequence
                                                (Sset _t'35
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _t'34 (tptr (Tstruct __COOItem noattr)))
                                                      (Tstruct __COOItem noattr))
                                                    _col tuint))
                                                (Ssequence
                                                  (Sset _t'36
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _bn (tptr (Tstruct __LLNode noattr)))
                                                        (Tstruct __LLNode noattr))
                                                      _item
                                                      (tptr (Tstruct __COOItem noattr))))
                                                  (Ssequence
                                                    (Sset _t'37
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _t'36 (tptr (Tstruct __COOItem noattr)))
                                                          (Tstruct __COOItem noattr))
                                                        _value tfloat))
                                                    (Scall (Some _t'4)
                                                      (Evar _COOItem_malloc 
                                                      (Tfunction
                                                        (Tcons tuint
                                                          (Tcons tuint
                                                            (Tcons tfloat
                                                              Tnil)))
                                                        (tptr (Tstruct __COOItem noattr))
                                                        cc_default))
                                                      ((Etempvar _t'33 tuint) ::
                                                       (Etempvar _t'35 tuint) ::
                                                       (Etempvar _t'37 tfloat) ::
                                                       nil))))))))
                                        (Sset _item
                                          (Etempvar _t'4 (tptr (Tstruct __COOItem noattr)))))
                                      (Ssequence
                                        (Sset _bn
                                          (Efield
                                            (Ederef
                                              (Etempvar _bn (tptr (Tstruct __LLNode noattr)))
                                              (Tstruct __LLNode noattr))
                                            _next
                                            (tptr (Tstruct __LLNode noattr))))
                                        (Sset _posY
                                          (Ebinop Oadd (Etempvar _posY tuint)
                                            (Econst_int (Int.repr 1) tint)
                                            tuint))))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'26
                                            (Efield
                                              (Ederef
                                                (Etempvar _an (tptr (Tstruct __LLNode noattr)))
                                                (Tstruct __LLNode noattr))
                                              _item
                                              (tptr (Tstruct __COOItem noattr))))
                                          (Ssequence
                                            (Sset _t'27
                                              (Efield
                                                (Ederef
                                                  (Etempvar _t'26 (tptr (Tstruct __COOItem noattr)))
                                                  (Tstruct __COOItem noattr))
                                                _row tuint))
                                            (Ssequence
                                              (Sset _t'28
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _an (tptr (Tstruct __LLNode noattr)))
                                                    (Tstruct __LLNode noattr))
                                                  _item
                                                  (tptr (Tstruct __COOItem noattr))))
                                              (Ssequence
                                                (Sset _t'29
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _t'28 (tptr (Tstruct __COOItem noattr)))
                                                      (Tstruct __COOItem noattr))
                                                    _col tuint))
                                                (Ssequence
                                                  (Sset _t'30
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _an (tptr (Tstruct __LLNode noattr)))
                                                        (Tstruct __LLNode noattr))
                                                      _item
                                                      (tptr (Tstruct __COOItem noattr))))
                                                  (Ssequence
                                                    (Sset _t'31
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _t'30 (tptr (Tstruct __COOItem noattr)))
                                                          (Tstruct __COOItem noattr))
                                                        _value tfloat))
                                                    (Scall (Some _t'5)
                                                      (Evar _COOItem_malloc 
                                                      (Tfunction
                                                        (Tcons tuint
                                                          (Tcons tuint
                                                            (Tcons tfloat
                                                              Tnil)))
                                                        (tptr (Tstruct __COOItem noattr))
                                                        cc_default))
                                                      ((Etempvar _t'27 tuint) ::
                                                       (Etempvar _t'29 tuint) ::
                                                       (Etempvar _t'31 tfloat) ::
                                                       nil))))))))
                                        (Sset _item
                                          (Etempvar _t'5 (tptr (Tstruct __COOItem noattr)))))
                                      (Ssequence
                                        (Sset _an
                                          (Efield
                                            (Ederef
                                              (Etempvar _an (tptr (Tstruct __LLNode noattr)))
                                              (Tstruct __LLNode noattr))
                                            _next
                                            (tptr (Tstruct __LLNode noattr))))
                                        (Sset _posX
                                          (Ebinop Oadd (Etempvar _posX tuint)
                                            (Econst_int (Int.repr 1) tint)
                                            tuint)))))
                                  (Scall None
                                    (Evar _COOChunk_push (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct __COOChunk noattr))
                                                             (Tcons
                                                               (tptr (Tstruct __COOItem noattr))
                                                               Tnil)) tvoid
                                                           cc_default))
                                    ((Eaddrof
                                       (Evar _temp (Tstruct __COOChunk noattr))
                                       (tptr (Tstruct __COOChunk noattr))) ::
                                     (Etempvar _item (tptr (Tstruct __COOItem noattr))) ::
                                     nil)))))
                            Sskip)
                          (Ssequence
                            (Sset _tempLen
                              (Efield
                                (Evar _temp (Tstruct __COOChunk noattr)) _len
                                tuint))
                            (Ssequence
                              (Sset _an
                                (Efield
                                  (Evar _temp (Tstruct __COOChunk noattr))
                                  _head (tptr (Tstruct __LLNode noattr))))
                              (Ssequence
                                (Ssequence
                                  (Sset _i__1 (Econst_int (Int.repr 0) tint))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _i__1 tuint)
                                                     (Etempvar _tempLen tuint)
                                                     tint)
                                        Sskip
                                        Sbreak)
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'22
                                              (Efield
                                                (Ederef
                                                  (Etempvar _an (tptr (Tstruct __LLNode noattr)))
                                                  (Tstruct __LLNode noattr))
                                                _next
                                                (tptr (Tstruct __LLNode noattr))))
                                            (Sifthenelse (Etempvar _t'22 (tptr (Tstruct __LLNode noattr)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'23
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _an (tptr (Tstruct __LLNode noattr)))
                                                        (Tstruct __LLNode noattr))
                                                      _item
                                                      (tptr (Tstruct __COOItem noattr))))
                                                  (Ssequence
                                                    (Sset _t'24
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _an (tptr (Tstruct __LLNode noattr)))
                                                          (Tstruct __LLNode noattr))
                                                        _next
                                                        (tptr (Tstruct __LLNode noattr))))
                                                    (Ssequence
                                                      (Sset _t'25
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _t'24 (tptr (Tstruct __LLNode noattr)))
                                                            (Tstruct __LLNode noattr))
                                                          _item
                                                          (tptr (Tstruct __COOItem noattr))))
                                                      (Scall (Some _t'7)
                                                        (Evar _posCmp 
                                                        (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct __COOItem noattr))
                                                            (Tcons
                                                              (tptr (Tstruct __COOItem noattr))
                                                              Tnil)) tint
                                                          cc_default))
                                                        ((Etempvar _t'23 (tptr (Tstruct __COOItem noattr))) ::
                                                         (Etempvar _t'25 (tptr (Tstruct __COOItem noattr))) ::
                                                         nil)))))
                                                (Sset _t'6
                                                  (Ecast
                                                    (Ebinop Oeq
                                                      (Etempvar _t'7 tint)
                                                      (Econst_int (Int.repr 0) tint)
                                                      tint) tbool)))
                                              (Sset _t'6
                                                (Econst_int (Int.repr 0) tint))))
                                          (Sifthenelse (Etempvar _t'6 tint)
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'16
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _an (tptr (Tstruct __LLNode noattr)))
                                                      (Tstruct __LLNode noattr))
                                                    _item
                                                    (tptr (Tstruct __COOItem noattr))))
                                                (Ssequence
                                                  (Sset _t'17
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _an (tptr (Tstruct __LLNode noattr)))
                                                        (Tstruct __LLNode noattr))
                                                      _item
                                                      (tptr (Tstruct __COOItem noattr))))
                                                  (Ssequence
                                                    (Sset _t'18
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _t'17 (tptr (Tstruct __COOItem noattr)))
                                                          (Tstruct __COOItem noattr))
                                                        _value tfloat))
                                                    (Ssequence
                                                      (Sset _t'19
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _an (tptr (Tstruct __LLNode noattr)))
                                                            (Tstruct __LLNode noattr))
                                                          _next
                                                          (tptr (Tstruct __LLNode noattr))))
                                                      (Ssequence
                                                        (Sset _t'20
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _t'19 (tptr (Tstruct __LLNode noattr)))
                                                              (Tstruct __LLNode noattr))
                                                            _item
                                                            (tptr (Tstruct __COOItem noattr))))
                                                        (Ssequence
                                                          (Sset _t'21
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _t'20 (tptr (Tstruct __COOItem noattr)))
                                                                (Tstruct __COOItem noattr))
                                                              _value tfloat))
                                                          (Sassign
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _t'16 (tptr (Tstruct __COOItem noattr)))
                                                                (Tstruct __COOItem noattr))
                                                              _value tfloat)
                                                            (Ebinop Oadd
                                                              (Etempvar _t'18 tfloat)
                                                              (Etempvar _t'21 tfloat)
                                                              tfloat))))))))
                                              (Ssequence
                                                (Sset _t'14
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _an (tptr (Tstruct __LLNode noattr)))
                                                      (Tstruct __LLNode noattr))
                                                    _next
                                                    (tptr (Tstruct __LLNode noattr))))
                                                (Ssequence
                                                  (Sset _t'15
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _t'14 (tptr (Tstruct __LLNode noattr)))
                                                        (Tstruct __LLNode noattr))
                                                      _item
                                                      (tptr (Tstruct __COOItem noattr))))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _t'15 (tptr (Tstruct __COOItem noattr)))
                                                        (Tstruct __COOItem noattr))
                                                      _value tfloat)
                                                    (Econst_int (Int.repr 0) tint)))))
                                            Sskip))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'13
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _an (tptr (Tstruct __LLNode noattr)))
                                                      (Tstruct __LLNode noattr))
                                                    _item
                                                    (tptr (Tstruct __COOItem noattr))))
                                                (Scall (Some _t'8)
                                                  (Evar _posCmp (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct __COOItem noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOItem noattr))
                                                                    Tnil))
                                                                  tint
                                                                  cc_default))
                                                  ((Etempvar _minBound (tptr (Tstruct __COOItem noattr))) ::
                                                   (Etempvar _t'13 (tptr (Tstruct __COOItem noattr))) ::
                                                   nil)))
                                              (Sifthenelse (Ebinop Ole
                                                             (Etempvar _t'8 tint)
                                                             (Econst_int (Int.repr 0) tint)
                                                             tint)
                                                (Sifthenelse (Eunop Onotbool
                                                               (Etempvar _maxBound (tptr (Tstruct __COOItem noattr)))
                                                               tint)
                                                  (Sset _t'9
                                                    (Ecast
                                                      (Econst_int (Int.repr 1) tint)
                                                      tbool))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'12
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _an (tptr (Tstruct __LLNode noattr)))
                                                              (Tstruct __LLNode noattr))
                                                            _item
                                                            (tptr (Tstruct __COOItem noattr))))
                                                        (Scall (Some _t'10)
                                                          (Evar _posCmp 
                                                          (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct __COOItem noattr))
                                                              (Tcons
                                                                (tptr (Tstruct __COOItem noattr))
                                                                Tnil)) tint
                                                            cc_default))
                                                          ((Etempvar _t'12 (tptr (Tstruct __COOItem noattr))) ::
                                                           (Etempvar _maxBound (tptr (Tstruct __COOItem noattr))) ::
                                                           nil)))
                                                      (Sset _t'9
                                                        (Ecast
                                                          (Ebinop Olt
                                                            (Etempvar _t'10 tint)
                                                            (Econst_int (Int.repr 0) tint)
                                                            tint) tbool)))
                                                    (Sset _t'9
                                                      (Ecast
                                                        (Etempvar _t'9 tint)
                                                        tbool))))
                                                (Sset _t'9
                                                  (Econst_int (Int.repr 0) tint))))
                                            (Sifthenelse (Eunop Onotbool
                                                           (Etempvar _t'9 tint)
                                                           tint)
                                              (Ssequence
                                                (Sset _t'11
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _an (tptr (Tstruct __LLNode noattr)))
                                                      (Tstruct __LLNode noattr))
                                                    _item
                                                    (tptr (Tstruct __COOItem noattr))))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _t'11 (tptr (Tstruct __COOItem noattr)))
                                                      (Tstruct __COOItem noattr))
                                                    _value tfloat)
                                                  (Econst_int (Int.repr 0) tint)))
                                              Sskip))
                                          (Sset _an
                                            (Efield
                                              (Ederef
                                                (Etempvar _an (tptr (Tstruct __LLNode noattr)))
                                                (Tstruct __LLNode noattr))
                                              _next
                                              (tptr (Tstruct __LLNode noattr)))))))
                                    (Sset _i__1
                                      (Ebinop Oadd (Etempvar _i__1 tuint)
                                        (Econst_int (Int.repr 1) tint) tuint))))
                                (Ssequence
                                  (Scall None
                                    (Evar _elimZero (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct __COOChunk noattr))
                                                        Tnil) tvoid
                                                      cc_default))
                                    ((Eaddrof
                                       (Evar _temp (Tstruct __COOChunk noattr))
                                       (tptr (Tstruct __COOChunk noattr))) ::
                                     nil))
                                  (Scall None
                                    (Evar _COOChunk_concat (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct __COOChunk noattr))
                                                               (Tcons
                                                                 (tptr (Tstruct __COOChunk noattr))
                                                                 Tnil)) tvoid
                                                             cc_default))
                                    ((Etempvar _result (tptr (Tstruct __COOChunk noattr))) ::
                                     (Eaddrof
                                       (Evar _temp (Tstruct __COOChunk noattr))
                                       (tptr (Tstruct __COOChunk noattr))) ::
                                     nil)))))))))))))))))))
|}.

Definition f_mergeTop := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_left, (tptr (Tstruct __COOChunk noattr))) ::
                (_right, (tptr (Tstruct __COOChunk noattr))) ::
                (_result, (tptr (Tstruct __COOChunk noattr))) ::
                (_lastDirection, tint) :: nil);
  fn_vars := ((_comp, (tarray (tarray tint 4) 4)) ::
              (_chunkA, (tarray (Tstruct __COOChunk noattr) 4)) ::
              (_chunkB, (tarray (Tstruct __COOChunk noattr) 4)) ::
              (_minBound, (Tstruct __COOItem noattr)) ::
              (_maxBound, (Tstruct __COOItem noattr)) :: nil);
  fn_temps := ((_lenLeft, tuint) :: (_lenRight, tuint) :: (_lenA, tuint) ::
               (_lenB, tuint) :: (_head, (tptr (Tstruct __LLNode noattr))) ::
               (_i, tuint) :: (_chunkLen, tuint) :: (_j, tuint) ::
               (_i__1, tuint) :: (_chunkLen__1, tuint) :: (_j__1, tuint) ::
               (_i__2, tuint) :: (_j__2, tuint) :: (_direction, tint) ::
               (_posX, tuint) :: (_posY, tuint) :: (_lastDir, tint) ::
               (_currComp, tint) ::
               (_currA, (tptr (Tstruct __COOChunk noattr))) ::
               (_currB, (tptr (Tstruct __COOChunk noattr))) ::
               (_maxChunk, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'11, tint) :: (_t'10, tint) :: (_t'9, tint) ::
               (_t'8, (tptr (Tstruct __COOChunk noattr))) :: (_t'7, tint) ::
               (_t'6, tint) :: (_t'5, tint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) ::
               (_t'41, (tptr (Tstruct __COOItem noattr))) ::
               (_t'40, (tptr (Tstruct __LLNode noattr))) ::
               (_t'39, (tptr (Tstruct __COOItem noattr))) ::
               (_t'38, (tptr (Tstruct __LLNode noattr))) :: (_t'37, tuint) ::
               (_t'36, (tptr (Tstruct __COOItem noattr))) ::
               (_t'35, (tptr (Tstruct __LLNode noattr))) :: (_t'34, tuint) ::
               (_t'33, (tptr (Tstruct __COOItem noattr))) ::
               (_t'32, (tptr (Tstruct __LLNode noattr))) :: (_t'31, tuint) ::
               (_t'30, (tptr (Tstruct __COOItem noattr))) ::
               (_t'29, (tptr (Tstruct __LLNode noattr))) :: (_t'28, tuint) ::
               (_t'27, (tptr (Tstruct __COOItem noattr))) ::
               (_t'26, (tptr (Tstruct __LLNode noattr))) :: (_t'25, tuint) ::
               (_t'24, tuint) :: (_t'23, tuint) ::
               (_t'22, (tptr (Tstruct __COOItem noattr))) ::
               (_t'21, (tptr (Tstruct __LLNode noattr))) :: (_t'20, tuint) ::
               (_t'19, (tptr (Tstruct __COOItem noattr))) ::
               (_t'18, (tptr (Tstruct __LLNode noattr))) :: (_t'17, tuint) ::
               (_t'16, tuint) :: (_t'15, tuint) :: (_t'14, tuint) ::
               (_t'13, tuint) :: (_t'12, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Ederef
          (Ebinop Oadd (Evar _comp (tarray (tarray tint 4) 4))
            (Econst_int (Int.repr 0) tint) (tptr (tarray tint 4)))
          (tarray tint 4)) (Econst_int (Int.repr 0) tint) (tptr tint)) tint)
    (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Ederef
            (Ebinop Oadd (Evar _comp (tarray (tarray tint 4) 4))
              (Econst_int (Int.repr 0) tint) (tptr (tarray tint 4)))
            (tarray tint 4)) (Econst_int (Int.repr 1) tint) (tptr tint))
        tint) (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Ederef
              (Ebinop Oadd (Evar _comp (tarray (tarray tint 4) 4))
                (Econst_int (Int.repr 0) tint) (tptr (tarray tint 4)))
              (tarray tint 4)) (Econst_int (Int.repr 2) tint) (tptr tint))
          tint) (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Ederef
                (Ebinop Oadd (Evar _comp (tarray (tarray tint 4) 4))
                  (Econst_int (Int.repr 0) tint) (tptr (tarray tint 4)))
                (tarray tint 4)) (Econst_int (Int.repr 3) tint) (tptr tint))
            tint) (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Ederef
                  (Ebinop Oadd (Evar _comp (tarray (tarray tint 4) 4))
                    (Econst_int (Int.repr 1) tint) (tptr (tarray tint 4)))
                  (tarray tint 4)) (Econst_int (Int.repr 0) tint)
                (tptr tint)) tint) (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Ederef
                    (Ebinop Oadd (Evar _comp (tarray (tarray tint 4) 4))
                      (Econst_int (Int.repr 1) tint) (tptr (tarray tint 4)))
                    (tarray tint 4)) (Econst_int (Int.repr 1) tint)
                  (tptr tint)) tint) (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Ederef
                      (Ebinop Oadd (Evar _comp (tarray (tarray tint 4) 4))
                        (Econst_int (Int.repr 1) tint)
                        (tptr (tarray tint 4))) (tarray tint 4))
                    (Econst_int (Int.repr 2) tint) (tptr tint)) tint)
                (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Ederef
                        (Ebinop Oadd (Evar _comp (tarray (tarray tint 4) 4))
                          (Econst_int (Int.repr 1) tint)
                          (tptr (tarray tint 4))) (tarray tint 4))
                      (Econst_int (Int.repr 3) tint) (tptr tint)) tint)
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Ederef
                          (Ebinop Oadd
                            (Evar _comp (tarray (tarray tint 4) 4))
                            (Econst_int (Int.repr 2) tint)
                            (tptr (tarray tint 4))) (tarray tint 4))
                        (Econst_int (Int.repr 0) tint) (tptr tint)) tint)
                    (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd
                          (Ederef
                            (Ebinop Oadd
                              (Evar _comp (tarray (tarray tint 4) 4))
                              (Econst_int (Int.repr 2) tint)
                              (tptr (tarray tint 4))) (tarray tint 4))
                          (Econst_int (Int.repr 1) tint) (tptr tint)) tint)
                      (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Ederef
                              (Ebinop Oadd
                                (Evar _comp (tarray (tarray tint 4) 4))
                                (Econst_int (Int.repr 2) tint)
                                (tptr (tarray tint 4))) (tarray tint 4))
                            (Econst_int (Int.repr 2) tint) (tptr tint)) tint)
                        (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _comp (tarray (tarray tint 4) 4))
                                  (Econst_int (Int.repr 2) tint)
                                  (tptr (tarray tint 4))) (tarray tint 4))
                              (Econst_int (Int.repr 3) tint) (tptr tint))
                            tint) (Econst_int (Int.repr 0) tint))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar _comp (tarray (tarray tint 4) 4))
                                    (Econst_int (Int.repr 3) tint)
                                    (tptr (tarray tint 4))) (tarray tint 4))
                                (Econst_int (Int.repr 0) tint) (tptr tint))
                              tint) (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _comp (tarray (tarray tint 4) 4))
                                      (Econst_int (Int.repr 3) tint)
                                      (tptr (tarray tint 4)))
                                    (tarray tint 4))
                                  (Econst_int (Int.repr 1) tint) (tptr tint))
                                tint) (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _comp (tarray (tarray tint 4) 4))
                                        (Econst_int (Int.repr 3) tint)
                                        (tptr (tarray tint 4)))
                                      (tarray tint 4))
                                    (Econst_int (Int.repr 2) tint)
                                    (tptr tint)) tint)
                                (Econst_int (Int.repr 0) tint))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _comp (tarray (tarray tint 4) 4))
                                          (Econst_int (Int.repr 3) tint)
                                          (tptr (tarray tint 4)))
                                        (tarray tint 4))
                                      (Econst_int (Int.repr 3) tint)
                                      (tptr tint)) tint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Sset _lenLeft
                                    (Efield
                                      (Ederef
                                        (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                                        (Tstruct __COOChunk noattr)) _len
                                      tuint))
                                  (Ssequence
                                    (Sset _lenRight
                                      (Efield
                                        (Ederef
                                          (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                                          (Tstruct __COOChunk noattr)) _len
                                        tuint))
                                    (Ssequence
                                      (Sset _lenA
                                        (Ebinop Odiv
                                          (Ebinop Oadd
                                            (Etempvar _lenLeft tuint)
                                            (Ebinop Osub
                                              (Econst_int (Int.repr 4) tint)
                                              (Econst_int (Int.repr 1) tint)
                                              tint) tuint)
                                          (Econst_int (Int.repr 4) tint)
                                          tuint))
                                      (Ssequence
                                        (Ssequence
                                          (Sifthenelse (Ebinop Ogt
                                                         (Etempvar _lenA tuint)
                                                         (Econst_int (Int.repr 4) tint)
                                                         tint)
                                            (Sset _t'1
                                              (Ecast
                                                (Econst_int (Int.repr 4) tint)
                                                tuint))
                                            (Sset _t'1
                                              (Ecast (Etempvar _lenA tuint)
                                                tuint)))
                                          (Sset _lenA (Etempvar _t'1 tuint)))
                                        (Ssequence
                                          (Sset _lenB
                                            (Ebinop Odiv
                                              (Ebinop Oadd
                                                (Etempvar _lenRight tuint)
                                                (Ebinop Osub
                                                  (Econst_int (Int.repr 4) tint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tint) tuint)
                                              (Econst_int (Int.repr 4) tint)
                                              tuint))
                                          (Ssequence
                                            (Ssequence
                                              (Sifthenelse (Ebinop Ogt
                                                             (Etempvar _lenB tuint)
                                                             (Econst_int (Int.repr 4) tint)
                                                             tint)
                                                (Sset _t'2
                                                  (Ecast
                                                    (Econst_int (Int.repr 4) tint)
                                                    tuint))
                                                (Sset _t'2
                                                  (Ecast
                                                    (Etempvar _lenB tuint)
                                                    tuint)))
                                              (Sset _lenB
                                                (Etempvar _t'2 tuint)))
                                            (Ssequence
                                              (Sset _head
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                                                    (Tstruct __COOChunk noattr))
                                                  _head
                                                  (tptr (Tstruct __LLNode noattr))))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _i
                                                    (Econst_int (Int.repr 0) tint))
                                                  (Sloop
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Olt
                                                                    (Etempvar _i tuint)
                                                                    (Etempvar _lenA tuint)
                                                                    tint)
                                                        Sskip
                                                        Sbreak)
                                                      (Ssequence
                                                        (Sset _chunkLen
                                                          (Ebinop Osub
                                                            (Etempvar _lenLeft tuint)
                                                            (Ebinop Omul
                                                              (Etempvar _i tuint)
                                                              (Econst_int (Int.repr 4) tint)
                                                              tuint) tuint))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop Olt
                                                                (Etempvar _chunkLen tuint)
                                                                (Econst_int (Int.repr 4) tint)
                                                                tint)
                                                              (Sset _t'3
                                                                (Ecast
                                                                  (Etempvar _chunkLen tuint)
                                                                  tuint))
                                                              (Sset _t'3
                                                                (Ecast
                                                                  (Econst_int (Int.repr 4) tint)
                                                                  tuint)))
                                                            (Sset _chunkLen
                                                              (Etempvar _t'3 tuint)))
                                                          (Ssequence
                                                            (Sassign
                                                              (Efield
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _chunkA (tarray (Tstruct __COOChunk noattr) 4))
                                                                    (Etempvar _i tuint)
                                                                    (tptr (Tstruct __COOChunk noattr)))
                                                                  (Tstruct __COOChunk noattr))
                                                                _len tuint)
                                                              (Etempvar _chunkLen tuint))
                                                            (Ssequence
                                                              (Sassign
                                                                (Efield
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _chunkA (tarray (Tstruct __COOChunk noattr) 4))
                                                                    (Etempvar _i tuint)
                                                                    (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                  _head
                                                                  (tptr (Tstruct __LLNode noattr)))
                                                                (Etempvar _head (tptr (Tstruct __LLNode noattr))))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _j
                                                                    (Econst_int (Int.repr 0) tint))
                                                                  (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _j tuint)
                                                                    (Ebinop Osub
                                                                    (Etempvar _chunkLen tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Sset _head
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _head (tptr (Tstruct __LLNode noattr)))
                                                                    (Tstruct __LLNode noattr))
                                                                    _next
                                                                    (tptr (Tstruct __LLNode noattr)))))
                                                                    (Sset _j
                                                                    (Ebinop Oadd
                                                                    (Etempvar _j tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))))
                                                                (Ssequence
                                                                  (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _chunkA (tarray (Tstruct __COOChunk noattr) 4))
                                                                    (Etempvar _i tuint)
                                                                    (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                    _tail
                                                                    (tptr (Tstruct __LLNode noattr)))
                                                                    (Etempvar _head (tptr (Tstruct __LLNode noattr))))
                                                                  (Sset _head
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _head (tptr (Tstruct __LLNode noattr)))
                                                                    (Tstruct __LLNode noattr))
                                                                    _next
                                                                    (tptr (Tstruct __LLNode noattr)))))))))))
                                                    (Sset _i
                                                      (Ebinop Oadd
                                                        (Etempvar _i tuint)
                                                        (Econst_int (Int.repr 1) tint)
                                                        tuint))))
                                                (Ssequence
                                                  (Sset _head
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                                                        (Tstruct __COOChunk noattr))
                                                      _head
                                                      (tptr (Tstruct __LLNode noattr))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _i__1
                                                        (Econst_int (Int.repr 0) tint))
                                                      (Sloop
                                                        (Ssequence
                                                          (Sifthenelse 
                                                            (Ebinop Olt
                                                              (Etempvar _i__1 tuint)
                                                              (Etempvar _lenB tuint)
                                                              tint)
                                                            Sskip
                                                            Sbreak)
                                                          (Ssequence
                                                            (Sset _chunkLen__1
                                                              (Ebinop Osub
                                                                (Etempvar _lenRight tuint)
                                                                (Ebinop Omul
                                                                  (Etempvar _i__1 tuint)
                                                                  (Econst_int (Int.repr 4) tint)
                                                                  tuint)
                                                                tuint))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sifthenelse 
                                                                  (Ebinop Olt
                                                                    (Etempvar _chunkLen__1 tuint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                  (Sset _t'4
                                                                    (Ecast
                                                                    (Etempvar _chunkLen__1 tuint)
                                                                    tuint))
                                                                  (Sset _t'4
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tuint)))
                                                                (Sset _chunkLen__1
                                                                  (Etempvar _t'4 tuint)))
                                                              (Ssequence
                                                                (Sassign
                                                                  (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _chunkB (tarray (Tstruct __COOChunk noattr) 4))
                                                                    (Etempvar _i__1 tuint)
                                                                    (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                    _len
                                                                    tuint)
                                                                  (Etempvar _chunkLen__1 tuint))
                                                                (Ssequence
                                                                  (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _chunkB (tarray (Tstruct __COOChunk noattr) 4))
                                                                    (Etempvar _i__1 tuint)
                                                                    (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                    _head
                                                                    (tptr (Tstruct __LLNode noattr)))
                                                                    (Etempvar _head (tptr (Tstruct __LLNode noattr))))
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _j__1
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _j__1 tuint)
                                                                    (Ebinop Osub
                                                                    (Etempvar _chunkLen__1 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Sset _head
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _head (tptr (Tstruct __LLNode noattr)))
                                                                    (Tstruct __LLNode noattr))
                                                                    _next
                                                                    (tptr (Tstruct __LLNode noattr)))))
                                                                    (Sset _j__1
                                                                    (Ebinop Oadd
                                                                    (Etempvar _j__1 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _chunkB (tarray (Tstruct __COOChunk noattr) 4))
                                                                    (Etempvar _i__1 tuint)
                                                                    (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                    _tail
                                                                    (tptr (Tstruct __LLNode noattr)))
                                                                    (Etempvar _head (tptr (Tstruct __LLNode noattr))))
                                                                    (Sset _head
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _head (tptr (Tstruct __LLNode noattr)))
                                                                    (Tstruct __LLNode noattr))
                                                                    _next
                                                                    (tptr (Tstruct __LLNode noattr)))))))))))
                                                        (Sset _i__1
                                                          (Ebinop Oadd
                                                            (Etempvar _i__1 tuint)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tuint))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _i__2
                                                          (Econst_int (Int.repr 0) tint))
                                                        (Sloop
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop Olt
                                                                (Etempvar _i__2 tuint)
                                                                (Etempvar _lenB tuint)
                                                                tint)
                                                              Sskip
                                                              Sbreak)
                                                            (Ssequence
                                                              (Sset _j__2
                                                                (Econst_int (Int.repr 0) tint))
                                                              (Sloop
                                                                (Ssequence
                                                                  (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _j__2 tuint)
                                                                    (Etempvar _lenA tuint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'38
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _chunkA (tarray (Tstruct __COOChunk noattr) 4))
                                                                    (Etempvar _j__2 tuint)
                                                                    (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                    _tail
                                                                    (tptr (Tstruct __LLNode noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'39
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'38 (tptr (Tstruct __LLNode noattr)))
                                                                    (Tstruct __LLNode noattr))
                                                                    _item
                                                                    (tptr (Tstruct __COOItem noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'40
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _chunkB (tarray (Tstruct __COOChunk noattr) 4))
                                                                    (Etempvar _i__2 tuint)
                                                                    (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                    _tail
                                                                    (tptr (Tstruct __LLNode noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'41
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'40 (tptr (Tstruct __LLNode noattr)))
                                                                    (Tstruct __LLNode noattr))
                                                                    _item
                                                                    (tptr (Tstruct __COOItem noattr))))
                                                                    (Scall (Some _t'5)
                                                                    (Evar _posCmp 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOItem noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOItem noattr))
                                                                    Tnil))
                                                                    tint
                                                                    cc_default))
                                                                    ((Etempvar _t'39 (tptr (Tstruct __COOItem noattr))) ::
                                                                    (Etempvar _t'41 (tptr (Tstruct __COOItem noattr))) ::
                                                                    nil))))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _t'5 tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sset _t'6
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))
                                                                    (Sset _t'6
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint))))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _comp (tarray (tarray tint 4) 4))
                                                                    (Etempvar _i__2 tuint)
                                                                    (tptr (tarray tint 4)))
                                                                    (tarray tint 4))
                                                                    (Etempvar _j__2 tuint)
                                                                    (tptr tint))
                                                                    tint)
                                                                    (Etempvar _t'6 tint))))
                                                                (Sset _j__2
                                                                  (Ebinop Oadd
                                                                    (Etempvar _j__2 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))))
                                                          (Sset _i__2
                                                            (Ebinop Oadd
                                                              (Etempvar _i__2 tuint)
                                                              (Econst_int (Int.repr 1) tint)
                                                              tuint))))
                                                      (Ssequence
                                                        (Sset _direction
                                                          (Etempvar _lastDirection tint))
                                                        (Ssequence
                                                          (Sset _posX
                                                            (Econst_int (Int.repr 0) tint))
                                                          (Ssequence
                                                            (Sset _posY
                                                              (Econst_int (Int.repr 0) tint))
                                                            (Ssequence
                                                              (Sswitch (Etempvar _direction tint)
                                                                (LScons (Some 1)
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'35
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _chunkA (tarray (Tstruct __COOChunk noattr) 4))
                                                                    (Etempvar _posX tuint)
                                                                    (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                    _head
                                                                    (tptr (Tstruct __LLNode noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'36
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'35 (tptr (Tstruct __LLNode noattr)))
                                                                    (Tstruct __LLNode noattr))
                                                                    _item
                                                                    (tptr (Tstruct __COOItem noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'37
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'36 (tptr (Tstruct __COOItem noattr)))
                                                                    (Tstruct __COOItem noattr))
                                                                    _row
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _maxBound (Tstruct __COOItem noattr))
                                                                    _row
                                                                    tuint)
                                                                    (Etempvar _t'37 tuint)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'32
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _chunkA (tarray (Tstruct __COOChunk noattr) 4))
                                                                    (Etempvar _posX tuint)
                                                                    (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                    _head
                                                                    (tptr (Tstruct __LLNode noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'33
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'32 (tptr (Tstruct __LLNode noattr)))
                                                                    (Tstruct __LLNode noattr))
                                                                    _item
                                                                    (tptr (Tstruct __COOItem noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'34
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'33 (tptr (Tstruct __COOItem noattr)))
                                                                    (Tstruct __COOItem noattr))
                                                                    _col
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _maxBound (Tstruct __COOItem noattr))
                                                                    _col
                                                                    tuint)
                                                                    (Etempvar _t'34 tuint)))))
                                                                    Sbreak))
                                                                  (LScons (Some 4294967295)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'29
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _chunkB (tarray (Tstruct __COOChunk noattr) 4))
                                                                    (Etempvar _posY tuint)
                                                                    (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                    _head
                                                                    (tptr (Tstruct __LLNode noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'30
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'29 (tptr (Tstruct __LLNode noattr)))
                                                                    (Tstruct __LLNode noattr))
                                                                    _item
                                                                    (tptr (Tstruct __COOItem noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'31
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'30 (tptr (Tstruct __COOItem noattr)))
                                                                    (Tstruct __COOItem noattr))
                                                                    _row
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _maxBound (Tstruct __COOItem noattr))
                                                                    _row
                                                                    tuint)
                                                                    (Etempvar _t'31 tuint)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'26
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _chunkB (tarray (Tstruct __COOChunk noattr) 4))
                                                                    (Etempvar _posY tuint)
                                                                    (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                    _head
                                                                    (tptr (Tstruct __LLNode noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'27
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'26 (tptr (Tstruct __LLNode noattr)))
                                                                    (Tstruct __LLNode noattr))
                                                                    _item
                                                                    (tptr (Tstruct __COOItem noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'28
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'27 (tptr (Tstruct __COOItem noattr)))
                                                                    (Tstruct __COOItem noattr))
                                                                    _col
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _maxBound (Tstruct __COOItem noattr))
                                                                    _col
                                                                    tuint)
                                                                    (Etempvar _t'28 tuint)))))
                                                                    Sbreak))
                                                                    (LScons None
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _maxBound (Tstruct __COOItem noattr))
                                                                    _row
                                                                    tuint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _maxBound (Tstruct __COOItem noattr))
                                                                    _col
                                                                    tuint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    Sbreak))
                                                                    LSnil))))
                                                              (Ssequence
                                                                (Sloop
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _posX tuint)
                                                                    (Etempvar _lenA tuint)
                                                                    tint)
                                                                    (Sset _t'7
                                                                    (Ecast
                                                                    (Ebinop Olt
                                                                    (Etempvar _posY tuint)
                                                                    (Etempvar _lenB tuint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'7
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'7 tint)
                                                                    Sskip
                                                                    Sbreak))
                                                                    (Ssequence
                                                                    (Sset _currComp
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _comp (tarray (tarray tint 4) 4))
                                                                    (Etempvar _posY tuint)
                                                                    (tptr (tarray tint 4)))
                                                                    (tarray tint 4))
                                                                    (Etempvar _posX tuint)
                                                                    (tptr tint))
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _currA
                                                                    (Ebinop Oadd
                                                                    (Evar _chunkA (tarray (Tstruct __COOChunk noattr) 4))
                                                                    (Etempvar _posX tuint)
                                                                    (tptr (Tstruct __COOChunk noattr))))
                                                                    (Ssequence
                                                                    (Sset _currB
                                                                    (Ebinop Oadd
                                                                    (Evar _chunkB (tarray (Tstruct __COOChunk noattr) 4))
                                                                    (Etempvar _posY tuint)
                                                                    (tptr (Tstruct __COOChunk noattr))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'25
                                                                    (Efield
                                                                    (Evar _maxBound (Tstruct __COOItem noattr))
                                                                    _row
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _minBound (Tstruct __COOItem noattr))
                                                                    _row
                                                                    tuint)
                                                                    (Etempvar _t'25 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'24
                                                                    (Efield
                                                                    (Evar _maxBound (Tstruct __COOItem noattr))
                                                                    _col
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _minBound (Tstruct __COOItem noattr))
                                                                    _col
                                                                    tuint)
                                                                    (Etempvar _t'24 tuint)))
                                                                    (Ssequence
                                                                    (Sset _lastDir
                                                                    (Etempvar _direction tint))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _currComp tint)
                                                                    (Ssequence
                                                                    (Sset _posY
                                                                    (Ebinop Oadd
                                                                    (Etempvar _posY tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Sset _direction
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Sset _posX
                                                                    (Ebinop Oadd
                                                                    (Etempvar _posX tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Sset _direction
                                                                    (Econst_int (Int.repr 1) tint))))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _posX tuint)
                                                                    (Etempvar _lenA tuint)
                                                                    tint)
                                                                    (Sset _t'11
                                                                    (Ecast
                                                                    (Ebinop Olt
                                                                    (Etempvar _posY tuint)
                                                                    (Etempvar _lenB tuint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'11
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'11 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _direction tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Sset _t'8
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Evar _chunkA (tarray (Tstruct __COOChunk noattr) 4))
                                                                    (Etempvar _posX tuint)
                                                                    (tptr (Tstruct __COOChunk noattr)))
                                                                    (tptr (Tstruct __COOChunk noattr))))
                                                                    (Sset _t'8
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Evar _chunkB (tarray (Tstruct __COOChunk noattr) 4))
                                                                    (Etempvar _posY tuint)
                                                                    (tptr (Tstruct __COOChunk noattr)))
                                                                    (tptr (Tstruct __COOChunk noattr)))))
                                                                    (Sset _maxChunk
                                                                    (Etempvar _t'8 (tptr (Tstruct __COOChunk noattr)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'21
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _maxChunk (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                    _head
                                                                    (tptr (Tstruct __LLNode noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'22
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'21 (tptr (Tstruct __LLNode noattr)))
                                                                    (Tstruct __LLNode noattr))
                                                                    _item
                                                                    (tptr (Tstruct __COOItem noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'23
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'22 (tptr (Tstruct __COOItem noattr)))
                                                                    (Tstruct __COOItem noattr))
                                                                    _row
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _maxBound (Tstruct __COOItem noattr))
                                                                    _row
                                                                    tuint)
                                                                    (Etempvar _t'23 tuint)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'18
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _maxChunk (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                    _head
                                                                    (tptr (Tstruct __LLNode noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'19
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'18 (tptr (Tstruct __LLNode noattr)))
                                                                    (Tstruct __LLNode noattr))
                                                                    _item
                                                                    (tptr (Tstruct __COOItem noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'20
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'19 (tptr (Tstruct __COOItem noattr)))
                                                                    (Tstruct __COOItem noattr))
                                                                    _col
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _maxBound (Tstruct __COOItem noattr))
                                                                    _col
                                                                    tuint)
                                                                    (Etempvar _t'20 tuint)))))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _mergeLow 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOItem noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOItem noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    Tnil)))))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _currA (tptr (Tstruct __COOChunk noattr))) ::
                                                                    (Etempvar _currB (tptr (Tstruct __COOChunk noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _minBound (Tstruct __COOItem noattr))
                                                                    (tptr (Tstruct __COOItem noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _maxBound (Tstruct __COOItem noattr))
                                                                    (tptr (Tstruct __COOItem noattr))) ::
                                                                    (Etempvar _result (tptr (Tstruct __COOChunk noattr))) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _direction tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'17
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _currA (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                    _len
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _COOChunk_freeNodes 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _left (tptr (Tstruct __COOChunk noattr))) ::
                                                                    (Etempvar _t'17 tuint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _t'16
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _currB (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                    _len
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _COOChunk_freeNodes 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _right (tptr (Tstruct __COOChunk noattr))) ::
                                                                    (Etempvar _t'16 tuint) ::
                                                                    nil))))))))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _posX tuint)
                                                                    (Etempvar _lenA tuint)
                                                                    tint)
                                                                    (Sset _t'10
                                                                    (Ecast
                                                                    (Ebinop Ole
                                                                    (Etempvar _lenLeft tuint)
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'10
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'10 tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _mergeLow 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOItem noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOItem noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    Tnil)))))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _currA (tptr (Tstruct __COOChunk noattr))) ::
                                                                    (Etempvar _currB (tptr (Tstruct __COOChunk noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _minBound (Tstruct __COOItem noattr))
                                                                    (tptr (Tstruct __COOItem noattr))) ::
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid)) ::
                                                                    (Etempvar _result (tptr (Tstruct __COOChunk noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'15
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                    _len
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _COOChunk_freeNodes 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _left (tptr (Tstruct __COOChunk noattr))) ::
                                                                    (Etempvar _t'15 tuint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _t'14
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _currB (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                    _len
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _COOChunk_freeNodes 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _right (tptr (Tstruct __COOChunk noattr))) ::
                                                                    (Etempvar _t'14 tuint) ::
                                                                    nil)))))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _posY tuint)
                                                                    (Etempvar _lenB tuint)
                                                                    tint)
                                                                    (Sset _t'9
                                                                    (Ecast
                                                                    (Ebinop Ole
                                                                    (Etempvar _lenRight tuint)
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'9
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'9 tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _mergeLow 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOItem noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOItem noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    Tnil)))))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _currA (tptr (Tstruct __COOChunk noattr))) ::
                                                                    (Etempvar _currB (tptr (Tstruct __COOChunk noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _minBound (Tstruct __COOItem noattr))
                                                                    (tptr (Tstruct __COOItem noattr))) ::
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid)) ::
                                                                    (Etempvar _result (tptr (Tstruct __COOChunk noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'13
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                    _len
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _COOChunk_freeNodes 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _right (tptr (Tstruct __COOChunk noattr))) ::
                                                                    (Etempvar _t'13 tuint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _t'12
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _currA (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tstruct __COOChunk noattr))
                                                                    _len
                                                                    tuint))
                                                                    (Scall None
                                                                    (Evar _COOChunk_freeNodes 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _left (tptr (Tstruct __COOChunk noattr))) ::
                                                                    (Etempvar _t'12 tuint) ::
                                                                    nil)))))
                                                                    (Sset _direction
                                                                    (Etempvar _lastDir tint))))))))))))))))
                                                                  Sskip)
                                                                (Sreturn (Some (Etempvar _direction tint)))))))))))))))))))))))))))))))))))
|}.

Definition f_elimZero := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_chunk, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_vars := ((_items, (tarray (tptr (Tstruct __COOItem noattr)) 8)) :: nil);
  fn_temps := ((_shift, tuint) :: (_zeroes, tuint) :: (_len, tuint) ::
               (_node, (tptr (Tstruct __LLNode noattr))) ::
               (_next, (tptr (Tstruct __LLNode noattr))) :: (_i, tuint) ::
               (_shouldShift, tint) :: (_i__1, tuint) :: (_i__2, tuint) ::
               (_i__3, tuint) :: (_t'1, (tptr tvoid)) ::
               (_t'17, (tptr (Tstruct __COOItem noattr))) ::
               (_t'16, tfloat) ::
               (_t'15, (tptr (Tstruct __COOItem noattr))) ::
               (_t'14, (tptr (Tstruct __COOItem noattr))) ::
               (_t'13, (tptr (Tstruct __COOItem noattr))) ::
               (_t'12, tuint) :: (_t'11, tfloat) ::
               (_t'10, (tptr (Tstruct __COOItem noattr))) ::
               (_t'9, (tptr (Tstruct __COOItem noattr))) :: (_t'8, tuint) ::
               (_t'7, (tptr (Tstruct __COOItem noattr))) ::
               (_t'6, (tptr (Tstruct __COOItem noattr))) :: (_t'5, tuint) ::
               (_t'4, (tptr (Tstruct __COOItem noattr))) ::
               (_t'3, (tptr (Tstruct __COOItem noattr))) ::
               (_t'2, (tptr (Tstruct __COOItem noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _shift (Econst_int (Int.repr 1) tint))
  (Ssequence
    (Sset _zeroes (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sset _len
        (Efield
          (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
            (Tstruct __COOChunk noattr)) _len tuint))
      (Ssequence
        (Sset _node
          (Efield
            (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _head
            (tptr (Tstruct __LLNode noattr))))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                               (Etempvar _len tuint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'15
                        (Efield
                          (Ederef
                            (Etempvar _node (tptr (Tstruct __LLNode noattr)))
                            (Tstruct __LLNode noattr)) _item
                          (tptr (Tstruct __COOItem noattr))))
                      (Ssequence
                        (Sset _t'16
                          (Efield
                            (Ederef
                              (Etempvar _t'15 (tptr (Tstruct __COOItem noattr)))
                              (Tstruct __COOItem noattr)) _value tfloat))
                        (Sifthenelse (Ebinop One (Etempvar _t'16 tfloat)
                                       (Econst_int (Int.repr 0) tint) tint)
                          (Ssequence
                            (Sset _t'17
                              (Efield
                                (Ederef
                                  (Etempvar _node (tptr (Tstruct __LLNode noattr)))
                                  (Tstruct __LLNode noattr)) _item
                                (tptr (Tstruct __COOItem noattr))))
                            (Sset _t'1
                              (Ecast
                                (Etempvar _t'17 (tptr (Tstruct __COOItem noattr)))
                                (tptr tvoid))))
                          (Sset _t'1
                            (Ecast
                              (Ecast (Econst_int (Int.repr 0) tint)
                                (tptr tvoid)) (tptr tvoid))))))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd
                          (Evar _items (tarray (tptr (Tstruct __COOItem noattr)) 8))
                          (Etempvar _i tuint)
                          (tptr (tptr (Tstruct __COOItem noattr))))
                        (tptr (Tstruct __COOItem noattr)))
                      (Etempvar _t'1 (tptr tvoid))))
                  (Sset _node
                    (Efield
                      (Ederef
                        (Etempvar _node (tptr (Tstruct __LLNode noattr)))
                        (Tstruct __LLNode noattr)) _next
                      (tptr (Tstruct __LLNode noattr))))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tuint)
                  (Econst_int (Int.repr 1) tint) tuint))))
          (Ssequence
            (Sset _shouldShift (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Swhile
                (Ebinop Olt (Etempvar _shift tuint) (Etempvar _len tuint)
                  tint)
                (Ssequence
                  (Sset _zeroes (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Ssequence
                      (Sset _i__1 (Econst_int (Int.repr 0) tint))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _i__1 tuint)
                                         (Etempvar _len tuint) tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Sset _shouldShift
                              (Ebinop Oand (Etempvar _zeroes tuint)
                                (Etempvar _shift tuint) tuint))
                            (Ssequence
                              (Ssequence
                                (Sset _t'14
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _items (tarray (tptr (Tstruct __COOItem noattr)) 8))
                                      (Etempvar _i__1 tuint)
                                      (tptr (tptr (Tstruct __COOItem noattr))))
                                    (tptr (Tstruct __COOItem noattr))))
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _t'14 (tptr (Tstruct __COOItem noattr)))
                                               (Ecast
                                                 (Econst_int (Int.repr 0) tint)
                                                 (tptr tvoid)) tint)
                                  (Sset _zeroes
                                    (Ebinop Oadd (Etempvar _zeroes tuint)
                                      (Econst_int (Int.repr 1) tint) tuint))
                                  Sskip))
                              (Sifthenelse (Etempvar _shouldShift tint)
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'13
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _items (tarray (tptr (Tstruct __COOItem noattr)) 8))
                                          (Etempvar _i__1 tuint)
                                          (tptr (tptr (Tstruct __COOItem noattr))))
                                        (tptr (Tstruct __COOItem noattr))))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _items (tarray (tptr (Tstruct __COOItem noattr)) 8))
                                          (Ebinop Osub (Etempvar _i__1 tuint)
                                            (Etempvar _shift tuint) tuint)
                                          (tptr (tptr (Tstruct __COOItem noattr))))
                                        (tptr (Tstruct __COOItem noattr)))
                                      (Etempvar _t'13 (tptr (Tstruct __COOItem noattr)))))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _items (tarray (tptr (Tstruct __COOItem noattr)) 8))
                                        (Etempvar _i__1 tuint)
                                        (tptr (tptr (Tstruct __COOItem noattr))))
                                      (tptr (Tstruct __COOItem noattr)))
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      (tptr tvoid))))
                                Sskip))))
                        (Sset _i__1
                          (Ebinop Oadd (Etempvar _i__1 tuint)
                            (Econst_int (Int.repr 1) tint) tuint))))
                    (Sset _shift
                      (Ebinop Omul (Etempvar _shift tuint)
                        (Econst_int (Int.repr 2) tint) tuint)))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
                      (Tstruct __COOChunk noattr)) _len tuint)
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
                        (Tstruct __COOChunk noattr)) _tail
                      (tptr (Tstruct __LLNode noattr)))
                    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                  (Ssequence
                    (Sset _node
                      (Efield
                        (Ederef
                          (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _head
                        (tptr (Tstruct __LLNode noattr))))
                    (Ssequence
                      (Ssequence
                        (Sset _i__2 (Econst_int (Int.repr 0) tint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _i__2 tuint)
                                           (Etempvar _len tuint) tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Sset _next
                                (Efield
                                  (Ederef
                                    (Etempvar _node (tptr (Tstruct __LLNode noattr)))
                                    (Tstruct __LLNode noattr)) _next
                                  (tptr (Tstruct __LLNode noattr))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'2
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _items (tarray (tptr (Tstruct __COOItem noattr)) 8))
                                        (Etempvar _i__2 tuint)
                                        (tptr (tptr (Tstruct __COOItem noattr))))
                                      (tptr (Tstruct __COOItem noattr))))
                                  (Sifthenelse (Etempvar _t'2 (tptr (Tstruct __COOItem noattr)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'12
                                          (Efield
                                            (Ederef
                                              (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
                                              (Tstruct __COOChunk noattr))
                                            _len tuint))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
                                              (Tstruct __COOChunk noattr))
                                            _len tuint)
                                          (Ebinop Oadd (Etempvar _t'12 tuint)
                                            (Econst_int (Int.repr 1) tint)
                                            tuint)))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'9
                                            (Efield
                                              (Ederef
                                                (Etempvar _node (tptr (Tstruct __LLNode noattr)))
                                                (Tstruct __LLNode noattr))
                                              _item
                                              (tptr (Tstruct __COOItem noattr))))
                                          (Ssequence
                                            (Sset _t'10
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _items (tarray (tptr (Tstruct __COOItem noattr)) 8))
                                                  (Etempvar _i__2 tuint)
                                                  (tptr (tptr (Tstruct __COOItem noattr))))
                                                (tptr (Tstruct __COOItem noattr))))
                                            (Ssequence
                                              (Sset _t'11
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _t'10 (tptr (Tstruct __COOItem noattr)))
                                                    (Tstruct __COOItem noattr))
                                                  _value tfloat))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _t'9 (tptr (Tstruct __COOItem noattr)))
                                                    (Tstruct __COOItem noattr))
                                                  _value tfloat)
                                                (Etempvar _t'11 tfloat)))))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'6
                                              (Efield
                                                (Ederef
                                                  (Etempvar _node (tptr (Tstruct __LLNode noattr)))
                                                  (Tstruct __LLNode noattr))
                                                _item
                                                (tptr (Tstruct __COOItem noattr))))
                                            (Ssequence
                                              (Sset _t'7
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _items (tarray (tptr (Tstruct __COOItem noattr)) 8))
                                                    (Etempvar _i__2 tuint)
                                                    (tptr (tptr (Tstruct __COOItem noattr))))
                                                  (tptr (Tstruct __COOItem noattr))))
                                              (Ssequence
                                                (Sset _t'8
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _t'7 (tptr (Tstruct __COOItem noattr)))
                                                      (Tstruct __COOItem noattr))
                                                    _col tuint))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _t'6 (tptr (Tstruct __COOItem noattr)))
                                                      (Tstruct __COOItem noattr))
                                                    _col tuint)
                                                  (Etempvar _t'8 tuint)))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'3
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _node (tptr (Tstruct __LLNode noattr)))
                                                    (Tstruct __LLNode noattr))
                                                  _item
                                                  (tptr (Tstruct __COOItem noattr))))
                                              (Ssequence
                                                (Sset _t'4
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _items (tarray (tptr (Tstruct __COOItem noattr)) 8))
                                                      (Etempvar _i__2 tuint)
                                                      (tptr (tptr (Tstruct __COOItem noattr))))
                                                    (tptr (Tstruct __COOItem noattr))))
                                                (Ssequence
                                                  (Sset _t'5
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _t'4 (tptr (Tstruct __COOItem noattr)))
                                                        (Tstruct __COOItem noattr))
                                                      _row tuint))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _t'3 (tptr (Tstruct __COOItem noattr)))
                                                        (Tstruct __COOItem noattr))
                                                      _row tuint)
                                                    (Etempvar _t'5 tuint)))))
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
                                                  (Tstruct __COOChunk noattr))
                                                _tail
                                                (tptr (Tstruct __LLNode noattr)))
                                              (Etempvar _node (tptr (Tstruct __LLNode noattr))))))))
                                    Sbreak))
                                (Sset _node
                                  (Etempvar _next (tptr (Tstruct __LLNode noattr)))))))
                          (Sset _i__2
                            (Ebinop Oadd (Etempvar _i__2 tuint)
                              (Econst_int (Int.repr 1) tint) tuint))))
                      (Ssequence
                        (Sset _i__3
                          (Efield
                            (Ederef
                              (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
                              (Tstruct __COOChunk noattr)) _len tuint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _i__3 tuint)
                                           (Etempvar _len tuint) tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Sset _next
                                (Efield
                                  (Ederef
                                    (Etempvar _node (tptr (Tstruct __LLNode noattr)))
                                    (Tstruct __LLNode noattr)) _next
                                  (tptr (Tstruct __LLNode noattr))))
                              (Ssequence
                                (Scall None
                                  (Evar _LLNode_freeAll (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct __LLNode noattr))
                                                            Tnil) tvoid
                                                          cc_default))
                                  ((Etempvar _node (tptr (Tstruct __LLNode noattr))) ::
                                   nil))
                                (Sset _node
                                  (Etempvar _next (tptr (Tstruct __LLNode noattr)))))))
                          (Sset _i__3
                            (Ebinop Oadd (Etempvar _i__3 tuint)
                              (Econst_int (Int.repr 1) tint) tuint)))))))))))))))
|}.

Definition f_mergeHier := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_left, (tptr (Tstruct __COOChunk noattr))) ::
                (_right, (tptr (Tstruct __COOChunk noattr))) ::
                (_result, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_direction, tint) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'20, (tptr (Tstruct __LLNode noattr))) ::
               (_t'19, (tptr (Tstruct __LLNode noattr))) :: (_t'18, tuint) ::
               (_t'17, (tptr (Tstruct __LLNode noattr))) ::
               (_t'16, (tptr (Tstruct __LLNode noattr))) ::
               (_t'15, (tptr (Tstruct __LLNode noattr))) :: (_t'14, tuint) ::
               (_t'13, (tptr (Tstruct __LLNode noattr))) ::
               (_t'12, (tptr (Tstruct __LLNode noattr))) :: (_t'11, tuint) ::
               (_t'10, tuint) :: (_t'9, tuint) :: (_t'8, tuint) ::
               (_t'7, (tptr (Tstruct __LLNode noattr))) ::
               (_t'6, (tptr (Tstruct __LLNode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
        (Tstruct __COOChunk noattr)) _len tuint)
    (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
          (Tstruct __COOChunk noattr)) _head
        (tptr (Tstruct __LLNode noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
            (Tstruct __COOChunk noattr)) _tail
          (tptr (Tstruct __LLNode noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Ssequence
        (Ssequence
          (Sifthenelse (Ebinop Oeq
                         (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Sset _t'3 (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Sset _t'20
                (Efield
                  (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                    (Tstruct __COOChunk noattr)) _head
                  (tptr (Tstruct __LLNode noattr))))
              (Sset _t'3
                (Ecast
                  (Ebinop Oeq
                    (Etempvar _t'20 (tptr (Tstruct __LLNode noattr)))
                    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
                  tbool))))
          (Sifthenelse (Etempvar _t'3 tint)
            (Ssequence
              (Ssequence
                (Sifthenelse (Ebinop Oeq
                               (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) tint)
                  (Sset _t'1 (Econst_int (Int.repr 1) tint))
                  (Ssequence
                    (Sset _t'19
                      (Efield
                        (Ederef
                          (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _head
                        (tptr (Tstruct __LLNode noattr))))
                    (Sset _t'1
                      (Ecast
                        (Ebinop Oeq
                          (Etempvar _t'19 (tptr (Tstruct __LLNode noattr)))
                          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                          tint) tbool))))
                (Sifthenelse (Etempvar _t'1 tint) (Sreturn None) Sskip))
              (Ssequence
                (Ssequence
                  (Sset _t'18
                    (Efield
                      (Ederef
                        (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                        (Tstruct __COOChunk noattr)) _len tuint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                        (Tstruct __COOChunk noattr)) _len tuint)
                    (Etempvar _t'18 tuint)))
                (Ssequence
                  (Ssequence
                    (Sset _t'17
                      (Efield
                        (Ederef
                          (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _head
                        (tptr (Tstruct __LLNode noattr))))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _head
                        (tptr (Tstruct __LLNode noattr)))
                      (Etempvar _t'17 (tptr (Tstruct __LLNode noattr)))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'16
                        (Efield
                          (Ederef
                            (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                            (Tstruct __COOChunk noattr)) _tail
                          (tptr (Tstruct __LLNode noattr))))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                            (Tstruct __COOChunk noattr)) _tail
                          (tptr (Tstruct __LLNode noattr)))
                        (Etempvar _t'16 (tptr (Tstruct __LLNode noattr)))))
                    (Sreturn None)))))
            (Ssequence
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Sset _t'2 (Econst_int (Int.repr 1) tint))
                (Ssequence
                  (Sset _t'15
                    (Efield
                      (Ederef
                        (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                        (Tstruct __COOChunk noattr)) _head
                      (tptr (Tstruct __LLNode noattr))))
                  (Sset _t'2
                    (Ecast
                      (Ebinop Oeq
                        (Etempvar _t'15 (tptr (Tstruct __LLNode noattr)))
                        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                        tint) tbool))))
              (Sifthenelse (Etempvar _t'2 tint)
                (Ssequence
                  (Ssequence
                    (Sset _t'14
                      (Efield
                        (Ederef
                          (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _len tuint))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _len tuint)
                      (Etempvar _t'14 tuint)))
                  (Ssequence
                    (Ssequence
                      (Sset _t'13
                        (Efield
                          (Ederef
                            (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                            (Tstruct __COOChunk noattr)) _head
                          (tptr (Tstruct __LLNode noattr))))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                            (Tstruct __COOChunk noattr)) _head
                          (tptr (Tstruct __LLNode noattr)))
                        (Etempvar _t'13 (tptr (Tstruct __LLNode noattr)))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'12
                          (Efield
                            (Ederef
                              (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                              (Tstruct __COOChunk noattr)) _tail
                            (tptr (Tstruct __LLNode noattr))))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                              (Tstruct __COOChunk noattr)) _tail
                            (tptr (Tstruct __LLNode noattr)))
                          (Etempvar _t'12 (tptr (Tstruct __LLNode noattr)))))
                      (Sreturn None))))
                Sskip))))
        (Ssequence
          (Sset _direction (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sloop
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'10
                      (Efield
                        (Ederef
                          (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _len tuint))
                    (Sifthenelse (Ebinop Ogt (Etempvar _t'10 tuint)
                                   (Econst_int (Int.repr 0) tint) tint)
                      (Ssequence
                        (Sset _t'11
                          (Efield
                            (Ederef
                              (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                              (Tstruct __COOChunk noattr)) _len tuint))
                        (Sset _t'4
                          (Ecast
                            (Ebinop Ogt (Etempvar _t'11 tuint)
                              (Econst_int (Int.repr 0) tint) tint) tbool)))
                      (Sset _t'4 (Econst_int (Int.repr 0) tint))))
                  (Sifthenelse (Etempvar _t'4 tint) Sskip Sbreak))
                (Ssequence
                  (Scall (Some _t'5)
                    (Evar _mergeTop (Tfunction
                                      (Tcons
                                        (tptr (Tstruct __COOChunk noattr))
                                        (Tcons
                                          (tptr (Tstruct __COOChunk noattr))
                                          (Tcons
                                            (tptr (Tstruct __COOChunk noattr))
                                            (Tcons tint Tnil)))) tint
                                      cc_default))
                    ((Etempvar _left (tptr (Tstruct __COOChunk noattr))) ::
                     (Etempvar _right (tptr (Tstruct __COOChunk noattr))) ::
                     (Etempvar _result (tptr (Tstruct __COOChunk noattr))) ::
                     (Etempvar _direction tint) :: nil))
                  (Sset _direction (Etempvar _t'5 tint))))
              Sskip)
            (Ssequence
              (Ssequence
                (Sset _t'9
                  (Efield
                    (Ederef
                      (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                      (Tstruct __COOChunk noattr)) _len tuint))
                (Sifthenelse (Ebinop Ogt (Etempvar _t'9 tuint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Scall None
                    (Evar _COOChunk_concat (Tfunction
                                             (Tcons
                                               (tptr (Tstruct __COOChunk noattr))
                                               (Tcons
                                                 (tptr (Tstruct __COOChunk noattr))
                                                 Tnil)) tvoid cc_default))
                    ((Etempvar _result (tptr (Tstruct __COOChunk noattr))) ::
                     (Etempvar _left (tptr (Tstruct __COOChunk noattr))) ::
                     nil))
                  Sskip))
              (Ssequence
                (Ssequence
                  (Sset _t'8
                    (Efield
                      (Ederef
                        (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                        (Tstruct __COOChunk noattr)) _len tuint))
                  (Sifthenelse (Ebinop Ogt (Etempvar _t'8 tuint)
                                 (Econst_int (Int.repr 0) tint) tint)
                    (Scall None
                      (Evar _COOChunk_concat (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct __COOChunk noattr))
                                                 (Tcons
                                                   (tptr (Tstruct __COOChunk noattr))
                                                   Tnil)) tvoid cc_default))
                      ((Etempvar _result (tptr (Tstruct __COOChunk noattr))) ::
                       (Etempvar _right (tptr (Tstruct __COOChunk noattr))) ::
                       nil))
                    Sskip))
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef
                        (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                        (Tstruct __COOChunk noattr)) _tail
                      (tptr (Tstruct __LLNode noattr))))
                  (Sifthenelse (Etempvar _t'6 (tptr (Tstruct __LLNode noattr)))
                    (Ssequence
                      (Sset _t'7
                        (Efield
                          (Ederef
                            (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                            (Tstruct __COOChunk noattr)) _tail
                          (tptr (Tstruct __LLNode noattr))))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _t'7 (tptr (Tstruct __LLNode noattr)))
                            (Tstruct __LLNode noattr)) _next
                          (tptr (Tstruct __LLNode noattr)))
                        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
                    Sskip))))))))))
|}.

Definition f_merge := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_left, (tptr (Tstruct __COOChunk noattr))) ::
                (_right, (tptr (Tstruct __COOChunk noattr))) ::
                (_result, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_li, (tptr (Tstruct __LLNode noattr))) ::
               (_ri, (tptr (Tstruct __LLNode noattr))) ::
               (_node, (tptr (Tstruct __LLNode noattr))) ::
               (_litem, (tptr (Tstruct __COOItem noattr))) ::
               (_ritem, (tptr (Tstruct __COOItem noattr))) ::
               (_item, (tptr (Tstruct __COOItem noattr))) ::
               (_tailItem, (tptr (Tstruct __COOItem noattr))) ::
               (_t'6, tint) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'27, (tptr (Tstruct __LLNode noattr))) ::
               (_t'26, (tptr (Tstruct __LLNode noattr))) :: (_t'25, tuint) ::
               (_t'24, (tptr (Tstruct __LLNode noattr))) ::
               (_t'23, (tptr (Tstruct __LLNode noattr))) ::
               (_t'22, (tptr (Tstruct __LLNode noattr))) :: (_t'21, tuint) ::
               (_t'20, (tptr (Tstruct __LLNode noattr))) ::
               (_t'19, (tptr (Tstruct __LLNode noattr))) ::
               (_t'18, (tptr (Tstruct __LLNode noattr))) :: (_t'17, tuint) ::
               (_t'16, tuint) :: (_t'15, tuint) :: (_t'14, tuint) ::
               (_t'13, tfloat) :: (_t'12, tfloat) :: (_t'11, tuint) ::
               (_t'10, (tptr (Tstruct __LLNode noattr))) ::
               (_t'9, (tptr (Tstruct __LLNode noattr))) ::
               (_t'8, (tptr (Tstruct __LLNode noattr))) ::
               (_t'7, (tptr (Tstruct __LLNode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
        (Tstruct __COOChunk noattr)) _len tuint)
    (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
          (Tstruct __COOChunk noattr)) _head
        (tptr (Tstruct __LLNode noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
            (Tstruct __COOChunk noattr)) _tail
          (tptr (Tstruct __LLNode noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Ssequence
        (Ssequence
          (Sifthenelse (Ebinop Oeq
                         (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Sset _t'3 (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Sset _t'27
                (Efield
                  (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                    (Tstruct __COOChunk noattr)) _head
                  (tptr (Tstruct __LLNode noattr))))
              (Sset _t'3
                (Ecast
                  (Ebinop Oeq
                    (Etempvar _t'27 (tptr (Tstruct __LLNode noattr)))
                    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
                  tbool))))
          (Sifthenelse (Etempvar _t'3 tint)
            (Ssequence
              (Ssequence
                (Sifthenelse (Ebinop Oeq
                               (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) tint)
                  (Sset _t'1 (Econst_int (Int.repr 1) tint))
                  (Ssequence
                    (Sset _t'26
                      (Efield
                        (Ederef
                          (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _head
                        (tptr (Tstruct __LLNode noattr))))
                    (Sset _t'1
                      (Ecast
                        (Ebinop Oeq
                          (Etempvar _t'26 (tptr (Tstruct __LLNode noattr)))
                          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                          tint) tbool))))
                (Sifthenelse (Etempvar _t'1 tint) (Sreturn None) Sskip))
              (Ssequence
                (Ssequence
                  (Sset _t'25
                    (Efield
                      (Ederef
                        (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                        (Tstruct __COOChunk noattr)) _len tuint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                        (Tstruct __COOChunk noattr)) _len tuint)
                    (Etempvar _t'25 tuint)))
                (Ssequence
                  (Ssequence
                    (Sset _t'24
                      (Efield
                        (Ederef
                          (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _head
                        (tptr (Tstruct __LLNode noattr))))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _head
                        (tptr (Tstruct __LLNode noattr)))
                      (Etempvar _t'24 (tptr (Tstruct __LLNode noattr)))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'23
                        (Efield
                          (Ederef
                            (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                            (Tstruct __COOChunk noattr)) _tail
                          (tptr (Tstruct __LLNode noattr))))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                            (Tstruct __COOChunk noattr)) _tail
                          (tptr (Tstruct __LLNode noattr)))
                        (Etempvar _t'23 (tptr (Tstruct __LLNode noattr)))))
                    (Sreturn None)))))
            (Ssequence
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Sset _t'2 (Econst_int (Int.repr 1) tint))
                (Ssequence
                  (Sset _t'22
                    (Efield
                      (Ederef
                        (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                        (Tstruct __COOChunk noattr)) _head
                      (tptr (Tstruct __LLNode noattr))))
                  (Sset _t'2
                    (Ecast
                      (Ebinop Oeq
                        (Etempvar _t'22 (tptr (Tstruct __LLNode noattr)))
                        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                        tint) tbool))))
              (Sifthenelse (Etempvar _t'2 tint)
                (Ssequence
                  (Ssequence
                    (Sset _t'21
                      (Efield
                        (Ederef
                          (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _len tuint))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _len tuint)
                      (Etempvar _t'21 tuint)))
                  (Ssequence
                    (Ssequence
                      (Sset _t'20
                        (Efield
                          (Ederef
                            (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                            (Tstruct __COOChunk noattr)) _head
                          (tptr (Tstruct __LLNode noattr))))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                            (Tstruct __COOChunk noattr)) _head
                          (tptr (Tstruct __LLNode noattr)))
                        (Etempvar _t'20 (tptr (Tstruct __LLNode noattr)))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'19
                          (Efield
                            (Ederef
                              (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                              (Tstruct __COOChunk noattr)) _tail
                            (tptr (Tstruct __LLNode noattr))))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                              (Tstruct __COOChunk noattr)) _tail
                            (tptr (Tstruct __LLNode noattr)))
                          (Etempvar _t'19 (tptr (Tstruct __LLNode noattr)))))
                      (Sreturn None))))
                Sskip))))
        (Ssequence
          (Sset _li
            (Efield
              (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                (Tstruct __COOChunk noattr)) _head
              (tptr (Tstruct __LLNode noattr))))
          (Ssequence
            (Sset _ri
              (Efield
                (Ederef (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                  (Tstruct __COOChunk noattr)) _head
                (tptr (Tstruct __LLNode noattr))))
            (Ssequence
              (Sloop
                (Ssequence
                  (Ssequence
                    (Sifthenelse (Ebinop Oeq
                                   (Etempvar _li (tptr (Tstruct __LLNode noattr)))
                                   (Ecast (Econst_int (Int.repr 0) tint)
                                     (tptr tvoid)) tint)
                      (Sset _t'4
                        (Ecast
                          (Ebinop Oeq
                            (Etempvar _ri (tptr (Tstruct __LLNode noattr)))
                            (Ecast (Econst_int (Int.repr 0) tint)
                              (tptr tvoid)) tint) tbool))
                      (Sset _t'4 (Econst_int (Int.repr 0) tint)))
                    (Sifthenelse (Eunop Onotbool (Etempvar _t'4 tint) tint)
                      Sskip
                      Sbreak))
                  (Ssequence
                    (Sifthenelse (Ebinop Oeq
                                   (Etempvar _li (tptr (Tstruct __LLNode noattr)))
                                   (Ecast (Econst_int (Int.repr 0) tint)
                                     (tptr tvoid)) tint)
                      (Ssequence
                        (Sset _node
                          (Etempvar _ri (tptr (Tstruct __LLNode noattr))))
                        (Sset _ri
                          (Efield
                            (Ederef
                              (Etempvar _ri (tptr (Tstruct __LLNode noattr)))
                              (Tstruct __LLNode noattr)) _next
                            (tptr (Tstruct __LLNode noattr)))))
                      (Sifthenelse (Ebinop Oeq
                                     (Etempvar _ri (tptr (Tstruct __LLNode noattr)))
                                     (Ecast (Econst_int (Int.repr 0) tint)
                                       (tptr tvoid)) tint)
                        (Ssequence
                          (Sset _node
                            (Etempvar _li (tptr (Tstruct __LLNode noattr))))
                          (Sset _li
                            (Efield
                              (Ederef
                                (Etempvar _li (tptr (Tstruct __LLNode noattr)))
                                (Tstruct __LLNode noattr)) _next
                              (tptr (Tstruct __LLNode noattr)))))
                        (Ssequence
                          (Sset _litem
                            (Efield
                              (Ederef
                                (Etempvar _li (tptr (Tstruct __LLNode noattr)))
                                (Tstruct __LLNode noattr)) _item
                              (tptr (Tstruct __COOItem noattr))))
                          (Ssequence
                            (Sset _ritem
                              (Efield
                                (Ederef
                                  (Etempvar _ri (tptr (Tstruct __LLNode noattr)))
                                  (Tstruct __LLNode noattr)) _item
                                (tptr (Tstruct __COOItem noattr))))
                            (Ssequence
                              (Scall (Some _t'5)
                                (Evar _posCmp (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct __COOItem noattr))
                                                  (Tcons
                                                    (tptr (Tstruct __COOItem noattr))
                                                    Tnil)) tint cc_default))
                                ((Etempvar _litem (tptr (Tstruct __COOItem noattr))) ::
                                 (Etempvar _ritem (tptr (Tstruct __COOItem noattr))) ::
                                 nil))
                              (Sifthenelse (Ebinop Olt (Etempvar _t'5 tint)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                (Ssequence
                                  (Sset _node
                                    (Etempvar _li (tptr (Tstruct __LLNode noattr))))
                                  (Sset _li
                                    (Efield
                                      (Ederef
                                        (Etempvar _li (tptr (Tstruct __LLNode noattr)))
                                        (Tstruct __LLNode noattr)) _next
                                      (tptr (Tstruct __LLNode noattr)))))
                                (Ssequence
                                  (Sset _node
                                    (Etempvar _ri (tptr (Tstruct __LLNode noattr))))
                                  (Sset _ri
                                    (Efield
                                      (Ederef
                                        (Etempvar _ri (tptr (Tstruct __LLNode noattr)))
                                        (Tstruct __LLNode noattr)) _next
                                      (tptr (Tstruct __LLNode noattr)))))))))))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _node (tptr (Tstruct __LLNode noattr)))
                            (Tstruct __LLNode noattr)) _next
                          (tptr (Tstruct __LLNode noattr)))
                        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                      (Ssequence
                        (Sset _item
                          (Efield
                            (Ederef
                              (Etempvar _node (tptr (Tstruct __LLNode noattr)))
                              (Tstruct __LLNode noattr)) _item
                            (tptr (Tstruct __COOItem noattr))))
                        (Ssequence
                          (Sset _t'9
                            (Efield
                              (Ederef
                                (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                                (Tstruct __COOChunk noattr)) _tail
                              (tptr (Tstruct __LLNode noattr))))
                          (Sifthenelse (Etempvar _t'9 (tptr (Tstruct __LLNode noattr)))
                            (Ssequence
                              (Ssequence
                                (Sset _t'18
                                  (Efield
                                    (Ederef
                                      (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                                      (Tstruct __COOChunk noattr)) _tail
                                    (tptr (Tstruct __LLNode noattr))))
                                (Sset _tailItem
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'18 (tptr (Tstruct __LLNode noattr)))
                                      (Tstruct __LLNode noattr)) _item
                                    (tptr (Tstruct __COOItem noattr)))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'14
                                    (Efield
                                      (Ederef
                                        (Etempvar _item (tptr (Tstruct __COOItem noattr)))
                                        (Tstruct __COOItem noattr)) _row
                                      tuint))
                                  (Ssequence
                                    (Sset _t'15
                                      (Efield
                                        (Ederef
                                          (Etempvar _tailItem (tptr (Tstruct __COOItem noattr)))
                                          (Tstruct __COOItem noattr)) _row
                                        tuint))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _t'14 tuint)
                                                   (Etempvar _t'15 tuint)
                                                   tint)
                                      (Ssequence
                                        (Sset _t'16
                                          (Efield
                                            (Ederef
                                              (Etempvar _item (tptr (Tstruct __COOItem noattr)))
                                              (Tstruct __COOItem noattr))
                                            _col tuint))
                                        (Ssequence
                                          (Sset _t'17
                                            (Efield
                                              (Ederef
                                                (Etempvar _tailItem (tptr (Tstruct __COOItem noattr)))
                                                (Tstruct __COOItem noattr))
                                              _col tuint))
                                          (Sset _t'6
                                            (Ecast
                                              (Ebinop Oeq
                                                (Etempvar _t'16 tuint)
                                                (Etempvar _t'17 tuint) tint)
                                              tbool))))
                                      (Sset _t'6
                                        (Econst_int (Int.repr 0) tint)))))
                                (Sifthenelse (Etempvar _t'6 tint)
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'12
                                        (Efield
                                          (Ederef
                                            (Etempvar _tailItem (tptr (Tstruct __COOItem noattr)))
                                            (Tstruct __COOItem noattr))
                                          _value tfloat))
                                      (Ssequence
                                        (Sset _t'13
                                          (Efield
                                            (Ederef
                                              (Etempvar _item (tptr (Tstruct __COOItem noattr)))
                                              (Tstruct __COOItem noattr))
                                            _value tfloat))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _tailItem (tptr (Tstruct __COOItem noattr)))
                                              (Tstruct __COOItem noattr))
                                            _value tfloat)
                                          (Ebinop Oadd
                                            (Etempvar _t'12 tfloat)
                                            (Etempvar _t'13 tfloat) tfloat))))
                                    (Scall None
                                      (Evar _LLNode_freeAll (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct __LLNode noattr))
                                                                Tnil) tvoid
                                                              cc_default))
                                      ((Etempvar _node (tptr (Tstruct __LLNode noattr))) ::
                                       nil)))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'11
                                        (Efield
                                          (Ederef
                                            (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                                            (Tstruct __COOChunk noattr)) _len
                                          tuint))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                                            (Tstruct __COOChunk noattr)) _len
                                          tuint)
                                        (Ebinop Oadd (Etempvar _t'11 tuint)
                                          (Econst_int (Int.repr 1) tint)
                                          tuint)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'10
                                          (Efield
                                            (Ederef
                                              (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                                              (Tstruct __COOChunk noattr))
                                            _tail
                                            (tptr (Tstruct __LLNode noattr))))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _t'10 (tptr (Tstruct __LLNode noattr)))
                                              (Tstruct __LLNode noattr))
                                            _next
                                            (tptr (Tstruct __LLNode noattr)))
                                          (Etempvar _node (tptr (Tstruct __LLNode noattr)))))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                                            (Tstruct __COOChunk noattr))
                                          _tail
                                          (tptr (Tstruct __LLNode noattr)))
                                        (Etempvar _node (tptr (Tstruct __LLNode noattr)))))))))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                                    (Tstruct __COOChunk noattr)) _len tuint)
                                (Econst_int (Int.repr 1) tint))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                                      (Tstruct __COOChunk noattr)) _head
                                    (tptr (Tstruct __LLNode noattr)))
                                  (Etempvar _node (tptr (Tstruct __LLNode noattr))))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                                      (Tstruct __COOChunk noattr)) _tail
                                    (tptr (Tstruct __LLNode noattr)))
                                  (Etempvar _node (tptr (Tstruct __LLNode noattr))))))))))))
                Sskip)
              (Ssequence
                (Sset _t'7
                  (Efield
                    (Ederef
                      (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                      (Tstruct __COOChunk noattr)) _tail
                    (tptr (Tstruct __LLNode noattr))))
                (Sifthenelse (Etempvar _t'7 (tptr (Tstruct __LLNode noattr)))
                  (Ssequence
                    (Sset _t'8
                      (Efield
                        (Ederef
                          (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _tail
                        (tptr (Tstruct __LLNode noattr))))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _t'8 (tptr (Tstruct __LLNode noattr)))
                          (Tstruct __LLNode noattr)) _next
                        (tptr (Tstruct __LLNode noattr)))
                      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
                  Sskip)))))))))
|}.

Definition f_flattenByMergeTree := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_chunks, (tptr (tptr (Tstruct __COOChunk noattr)))) ::
                (_len, tuint) ::
                (_result, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_currLen, tuint) ::
               (_merger, (tptr (Tstruct __COOChunk noattr))) ::
               (_temp, (tptr (Tstruct __COOChunk noattr))) :: (_i, tuint) ::
               (_nextLen, tuint) :: (_i__1, tuint) ::
               (_left, (tptr (Tstruct __COOChunk noattr))) ::
               (_right, (tptr (Tstruct __COOChunk noattr))) ::
               (_i__2, tuint) :: (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'21, tuint) ::
               (_t'20, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'19, (tptr (Tstruct __LLNode noattr))) ::
               (_t'18, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'17, (tptr (Tstruct __LLNode noattr))) ::
               (_t'16, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'15, tuint) ::
               (_t'14, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'13, (tptr (Tstruct __LLNode noattr))) ::
               (_t'12, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'11, (tptr (Tstruct __LLNode noattr))) ::
               (_t'10, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'9, tuint) :: (_t'8, (tptr (Tstruct __LLNode noattr))) ::
               (_t'7, (tptr (Tstruct __LLNode noattr))) :: (_t'6, tuint) ::
               (_t'5, (tptr (Tstruct __LLNode noattr))) ::
               (_t'4, (tptr (Tstruct __LLNode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole (Etempvar _len tuint)
                 (Econst_int (Int.repr 0) tint) tint)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
            (Tstruct __COOChunk noattr)) _len tuint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _head
            (tptr (Tstruct __LLNode noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                (Tstruct __COOChunk noattr)) _tail
              (tptr (Tstruct __LLNode noattr)))
            (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
          (Sreturn None))))
    (Sifthenelse (Ebinop Oeq (Etempvar _len tuint)
                   (Econst_int (Int.repr 1) tint) tint)
      (Ssequence
        (Ssequence
          (Sset _t'20
            (Ederef
              (Ebinop Oadd
                (Etempvar _chunks (tptr (tptr (Tstruct __COOChunk noattr))))
                (Econst_int (Int.repr 0) tint)
                (tptr (tptr (Tstruct __COOChunk noattr))))
              (tptr (Tstruct __COOChunk noattr))))
          (Ssequence
            (Sset _t'21
              (Efield
                (Ederef (Etempvar _t'20 (tptr (Tstruct __COOChunk noattr)))
                  (Tstruct __COOChunk noattr)) _len tuint))
            (Sassign
              (Efield
                (Ederef (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                  (Tstruct __COOChunk noattr)) _len tuint)
              (Etempvar _t'21 tuint))))
        (Ssequence
          (Ssequence
            (Sset _t'18
              (Ederef
                (Ebinop Oadd
                  (Etempvar _chunks (tptr (tptr (Tstruct __COOChunk noattr))))
                  (Econst_int (Int.repr 0) tint)
                  (tptr (tptr (Tstruct __COOChunk noattr))))
                (tptr (Tstruct __COOChunk noattr))))
            (Ssequence
              (Sset _t'19
                (Efield
                  (Ederef (Etempvar _t'18 (tptr (Tstruct __COOChunk noattr)))
                    (Tstruct __COOChunk noattr)) _head
                  (tptr (Tstruct __LLNode noattr))))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                    (Tstruct __COOChunk noattr)) _head
                  (tptr (Tstruct __LLNode noattr)))
                (Etempvar _t'19 (tptr (Tstruct __LLNode noattr))))))
          (Ssequence
            (Ssequence
              (Sset _t'16
                (Ederef
                  (Ebinop Oadd
                    (Etempvar _chunks (tptr (tptr (Tstruct __COOChunk noattr))))
                    (Econst_int (Int.repr 0) tint)
                    (tptr (tptr (Tstruct __COOChunk noattr))))
                  (tptr (Tstruct __COOChunk noattr))))
              (Ssequence
                (Sset _t'17
                  (Efield
                    (Ederef
                      (Etempvar _t'16 (tptr (Tstruct __COOChunk noattr)))
                      (Tstruct __COOChunk noattr)) _tail
                    (tptr (Tstruct __LLNode noattr))))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                      (Tstruct __COOChunk noattr)) _tail
                    (tptr (Tstruct __LLNode noattr)))
                  (Etempvar _t'17 (tptr (Tstruct __LLNode noattr))))))
            (Sreturn None))))
      Sskip))
  (Ssequence
    (Sset _currLen (Etempvar _len tuint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                          cc_default))
          ((Ebinop Omul (Etempvar _len tuint)
             (Esizeof (Tstruct __COOChunk noattr) tuint) tuint) :: nil))
        (Sset _merger
          (Ecast (Etempvar _t'1 (tptr tvoid))
            (tptr (Tstruct __COOChunk noattr)))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                            cc_default))
            ((Ebinop Omul
               (Ebinop Oadd
                 (Ebinop Odiv (Etempvar _len tuint)
                   (Econst_int (Int.repr 2) tint) tuint)
                 (Econst_int (Int.repr 1) tint) tuint)
               (Esizeof (Tstruct __COOChunk noattr) tuint) tuint) :: nil))
          (Sset _temp
            (Ecast (Etempvar _t'2 (tptr tvoid))
              (tptr (Tstruct __COOChunk noattr)))))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                               (Etempvar _len tuint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Sset _t'14
                      (Ederef
                        (Ebinop Oadd
                          (Etempvar _chunks (tptr (tptr (Tstruct __COOChunk noattr))))
                          (Etempvar _i tuint)
                          (tptr (tptr (Tstruct __COOChunk noattr))))
                        (tptr (Tstruct __COOChunk noattr))))
                    (Ssequence
                      (Sset _t'15
                        (Efield
                          (Ederef
                            (Etempvar _t'14 (tptr (Tstruct __COOChunk noattr)))
                            (Tstruct __COOChunk noattr)) _len tuint))
                      (Sassign
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Etempvar _merger (tptr (Tstruct __COOChunk noattr)))
                              (Etempvar _i tuint)
                              (tptr (Tstruct __COOChunk noattr)))
                            (Tstruct __COOChunk noattr)) _len tuint)
                        (Etempvar _t'15 tuint))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'12
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _chunks (tptr (tptr (Tstruct __COOChunk noattr))))
                            (Etempvar _i tuint)
                            (tptr (tptr (Tstruct __COOChunk noattr))))
                          (tptr (Tstruct __COOChunk noattr))))
                      (Ssequence
                        (Sset _t'13
                          (Efield
                            (Ederef
                              (Etempvar _t'12 (tptr (Tstruct __COOChunk noattr)))
                              (Tstruct __COOChunk noattr)) _head
                            (tptr (Tstruct __LLNode noattr))))
                        (Sassign
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Etempvar _merger (tptr (Tstruct __COOChunk noattr)))
                                (Etempvar _i tuint)
                                (tptr (Tstruct __COOChunk noattr)))
                              (Tstruct __COOChunk noattr)) _head
                            (tptr (Tstruct __LLNode noattr)))
                          (Etempvar _t'13 (tptr (Tstruct __LLNode noattr))))))
                    (Ssequence
                      (Sset _t'10
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _chunks (tptr (tptr (Tstruct __COOChunk noattr))))
                            (Etempvar _i tuint)
                            (tptr (tptr (Tstruct __COOChunk noattr))))
                          (tptr (Tstruct __COOChunk noattr))))
                      (Ssequence
                        (Sset _t'11
                          (Efield
                            (Ederef
                              (Etempvar _t'10 (tptr (Tstruct __COOChunk noattr)))
                              (Tstruct __COOChunk noattr)) _tail
                            (tptr (Tstruct __LLNode noattr))))
                        (Sassign
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Etempvar _merger (tptr (Tstruct __COOChunk noattr)))
                                (Etempvar _i tuint)
                                (tptr (Tstruct __COOChunk noattr)))
                              (Tstruct __COOChunk noattr)) _tail
                            (tptr (Tstruct __LLNode noattr)))
                          (Etempvar _t'11 (tptr (Tstruct __LLNode noattr)))))))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tuint)
                  (Econst_int (Int.repr 1) tint) tuint))))
          (Ssequence
            (Swhile
              (Ebinop Ogt (Etempvar _currLen tuint)
                (Econst_int (Int.repr 1) tint) tint)
              (Ssequence
                (Sset _nextLen
                  (Ebinop Odiv
                    (Ebinop Oadd (Etempvar _currLen tuint)
                      (Econst_int (Int.repr 1) tint) tuint)
                    (Econst_int (Int.repr 2) tint) tuint))
                (Ssequence
                  (Ssequence
                    (Sset _i__1 (Econst_int (Int.repr 0) tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _i__1 tuint)
                                       (Etempvar _nextLen tuint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Sset _left
                            (Ebinop Oadd
                              (Etempvar _merger (tptr (Tstruct __COOChunk noattr)))
                              (Ebinop Omul (Econst_int (Int.repr 2) tint)
                                (Etempvar _i__1 tuint) tuint)
                              (tptr (Tstruct __COOChunk noattr))))
                          (Ssequence
                            (Ssequence
                              (Sifthenelse (Ebinop Oge
                                             (Ebinop Oadd
                                               (Ebinop Omul
                                                 (Econst_int (Int.repr 2) tint)
                                                 (Etempvar _i__1 tuint)
                                                 tuint)
                                               (Econst_int (Int.repr 1) tint)
                                               tuint)
                                             (Etempvar _currLen tuint) tint)
                                (Sset _t'3
                                  (Ecast
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      (tptr tvoid)) (tptr tvoid)))
                                (Sset _t'3
                                  (Ecast
                                    (Ebinop Oadd
                                      (Etempvar _merger (tptr (Tstruct __COOChunk noattr)))
                                      (Ebinop Oadd
                                        (Ebinop Omul
                                          (Econst_int (Int.repr 2) tint)
                                          (Etempvar _i__1 tuint) tuint)
                                        (Econst_int (Int.repr 1) tint) tuint)
                                      (tptr (Tstruct __COOChunk noattr)))
                                    (tptr tvoid))))
                              (Sset _right (Etempvar _t'3 (tptr tvoid))))
                            (Scall None
                              (Evar _mergeHier (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct __COOChunk noattr))
                                                   (Tcons
                                                     (tptr (Tstruct __COOChunk noattr))
                                                     (Tcons
                                                       (tptr (Tstruct __COOChunk noattr))
                                                       Tnil))) tvoid
                                                 cc_default))
                              ((Etempvar _left (tptr (Tstruct __COOChunk noattr))) ::
                               (Etempvar _right (tptr (Tstruct __COOChunk noattr))) ::
                               (Ebinop Oadd
                                 (Etempvar _temp (tptr (Tstruct __COOChunk noattr)))
                                 (Etempvar _i__1 tuint)
                                 (tptr (Tstruct __COOChunk noattr))) :: nil)))))
                      (Sset _i__1
                        (Ebinop Oadd (Etempvar _i__1 tuint)
                          (Econst_int (Int.repr 1) tint) tuint))))
                  (Ssequence
                    (Ssequence
                      (Sset _i__2 (Econst_int (Int.repr 0) tint))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _i__2 tuint)
                                         (Etempvar _nextLen tuint) tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Ssequence
                              (Sset _t'9
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _temp (tptr (Tstruct __COOChunk noattr)))
                                      (Etempvar _i__2 tuint)
                                      (tptr (Tstruct __COOChunk noattr)))
                                    (Tstruct __COOChunk noattr)) _len tuint))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _merger (tptr (Tstruct __COOChunk noattr)))
                                      (Etempvar _i__2 tuint)
                                      (tptr (Tstruct __COOChunk noattr)))
                                    (Tstruct __COOChunk noattr)) _len tuint)
                                (Etempvar _t'9 tuint)))
                            (Ssequence
                              (Ssequence
                                (Sset _t'8
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _temp (tptr (Tstruct __COOChunk noattr)))
                                        (Etempvar _i__2 tuint)
                                        (tptr (Tstruct __COOChunk noattr)))
                                      (Tstruct __COOChunk noattr)) _head
                                    (tptr (Tstruct __LLNode noattr))))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _merger (tptr (Tstruct __COOChunk noattr)))
                                        (Etempvar _i__2 tuint)
                                        (tptr (Tstruct __COOChunk noattr)))
                                      (Tstruct __COOChunk noattr)) _head
                                    (tptr (Tstruct __LLNode noattr)))
                                  (Etempvar _t'8 (tptr (Tstruct __LLNode noattr)))))
                              (Ssequence
                                (Sset _t'7
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _temp (tptr (Tstruct __COOChunk noattr)))
                                        (Etempvar _i__2 tuint)
                                        (tptr (Tstruct __COOChunk noattr)))
                                      (Tstruct __COOChunk noattr)) _tail
                                    (tptr (Tstruct __LLNode noattr))))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _merger (tptr (Tstruct __COOChunk noattr)))
                                        (Etempvar _i__2 tuint)
                                        (tptr (Tstruct __COOChunk noattr)))
                                      (Tstruct __COOChunk noattr)) _tail
                                    (tptr (Tstruct __LLNode noattr)))
                                  (Etempvar _t'7 (tptr (Tstruct __LLNode noattr))))))))
                        (Sset _i__2
                          (Ebinop Oadd (Etempvar _i__2 tuint)
                            (Econst_int (Int.repr 1) tint) tuint))))
                    (Sset _currLen (Etempvar _nextLen tuint))))))
            (Ssequence
              (Ssequence
                (Sset _t'6
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Etempvar _merger (tptr (Tstruct __COOChunk noattr)))
                        (Econst_int (Int.repr 0) tint)
                        (tptr (Tstruct __COOChunk noattr)))
                      (Tstruct __COOChunk noattr)) _len tuint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                      (Tstruct __COOChunk noattr)) _len tuint)
                  (Etempvar _t'6 tuint)))
              (Ssequence
                (Ssequence
                  (Sset _t'5
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Etempvar _merger (tptr (Tstruct __COOChunk noattr)))
                          (Econst_int (Int.repr 0) tint)
                          (tptr (Tstruct __COOChunk noattr)))
                        (Tstruct __COOChunk noattr)) _head
                      (tptr (Tstruct __LLNode noattr))))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                        (Tstruct __COOChunk noattr)) _head
                      (tptr (Tstruct __LLNode noattr)))
                    (Etempvar _t'5 (tptr (Tstruct __LLNode noattr)))))
                (Ssequence
                  (Ssequence
                    (Sset _t'4
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _merger (tptr (Tstruct __COOChunk noattr)))
                            (Econst_int (Int.repr 0) tint)
                            (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _tail
                        (tptr (Tstruct __LLNode noattr))))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _tail
                        (tptr (Tstruct __LLNode noattr)))
                      (Etempvar _t'4 (tptr (Tstruct __LLNode noattr)))))
                  (Ssequence
                    (Scall None
                      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                    cc_default))
                      ((Etempvar _merger (tptr (Tstruct __COOChunk noattr))) ::
                       nil))
                    (Scall None
                      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                    cc_default))
                      ((Etempvar _temp (tptr (Tstruct __COOChunk noattr))) ::
                       nil))))))))))))
|}.

Definition f_condense := {|
  fn_return := (tptr (tptr (Tstruct __COOChunk noattr)));
  fn_callconv := cc_default;
  fn_params := ((_csr, (tptr (Tstruct __CSRMatrix noattr))) ::
                (_outLen, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_len, tuint) :: (_i, tuint) :: (_rowCnt, tuint) ::
               (_chunks, (tptr (tptr (Tstruct __COOChunk noattr)))) ::
               (_height, tuint) :: (_i__1, tuint) ::
               (_chunk, (tptr (Tstruct __COOChunk noattr))) :: (_j, tuint) ::
               (_rowCnt__1, tuint) :: (_idx, tuint) :: (_col, tuint) ::
               (_value, tfloat) ::
               (_item, (tptr (Tstruct __COOItem noattr))) ::
               (_t'3, (tptr (Tstruct __COOItem noattr))) ::
               (_t'2, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'1, (tptr tvoid)) :: (_t'16, tuint) :: (_t'15, tuint) ::
               (_t'14, (tptr tuint)) :: (_t'13, tuint) ::
               (_t'12, (tptr tuint)) :: (_t'11, tuint) ::
               (_t'10, (tptr tuint)) :: (_t'9, tuint) ::
               (_t'8, (tptr tuint)) :: (_t'7, tuint) ::
               (_t'6, (tptr tuint)) :: (_t'5, (tptr tuint)) ::
               (_t'4, (tptr tfloat)) :: nil);
  fn_body :=
(Ssequence
  (Sset _len (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Ssequence
            (Sset _t'16
              (Efield
                (Ederef (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                  (Tstruct __CSRMatrix noattr)) _height tuint))
            (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                           (Etempvar _t'16 tuint) tint)
              Sskip
              Sbreak))
          (Ssequence
            (Ssequence
              (Sset _t'12
                (Efield
                  (Ederef (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                    (Tstruct __CSRMatrix noattr)) _rows (tptr tuint)))
              (Ssequence
                (Sset _t'13
                  (Ederef
                    (Ebinop Oadd (Etempvar _t'12 (tptr tuint))
                      (Ebinop Oadd (Etempvar _i tuint)
                        (Econst_int (Int.repr 1) tint) tuint) (tptr tuint))
                    tuint))
                (Ssequence
                  (Sset _t'14
                    (Efield
                      (Ederef
                        (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                        (Tstruct __CSRMatrix noattr)) _rows (tptr tuint)))
                  (Ssequence
                    (Sset _t'15
                      (Ederef
                        (Ebinop Oadd (Etempvar _t'14 (tptr tuint))
                          (Etempvar _i tuint) (tptr tuint)) tuint))
                    (Sset _rowCnt
                      (Ebinop Osub (Etempvar _t'13 tuint)
                        (Etempvar _t'15 tuint) tuint))))))
            (Sifthenelse (Ebinop Ogt (Etempvar _rowCnt tuint)
                           (Etempvar _len tuint) tint)
              (Sset _len (Etempvar _rowCnt tuint))
              Sskip)))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Ssequence
      (Sassign (Ederef (Etempvar _outLen (tptr tuint)) tuint)
        (Etempvar _len tuint))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                            cc_default))
            ((Ebinop Omul (Etempvar _len tuint)
               (Esizeof (tptr (Tstruct __COOChunk noattr)) tuint) tuint) ::
             nil))
          (Sset _chunks
            (Ecast (Etempvar _t'1 (tptr tvoid))
              (tptr (tptr (Tstruct __COOChunk noattr))))))
        (Ssequence
          (Sset _height
            (Efield
              (Ederef (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                (Tstruct __CSRMatrix noattr)) _height tuint))
          (Ssequence
            (Ssequence
              (Sset _i__1 (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i__1 tuint)
                                 (Etempvar _len tuint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'2)
                        (Evar _COOChunk_malloc (Tfunction Tnil
                                                 (tptr (Tstruct __COOChunk noattr))
                                                 cc_default)) nil)
                      (Sset _chunk
                        (Etempvar _t'2 (tptr (Tstruct __COOChunk noattr)))))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _chunks (tptr (tptr (Tstruct __COOChunk noattr))))
                            (Etempvar _i__1 tuint)
                            (tptr (tptr (Tstruct __COOChunk noattr))))
                          (tptr (Tstruct __COOChunk noattr)))
                        (Etempvar _chunk (tptr (Tstruct __COOChunk noattr))))
                      (Ssequence
                        (Sset _j (Econst_int (Int.repr 0) tint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _j tuint)
                                           (Etempvar _height tuint) tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Ssequence
                                (Sset _t'8
                                  (Efield
                                    (Ederef
                                      (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                      (Tstruct __CSRMatrix noattr)) _rows
                                    (tptr tuint)))
                                (Ssequence
                                  (Sset _t'9
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _t'8 (tptr tuint))
                                        (Ebinop Oadd (Etempvar _j tuint)
                                          (Econst_int (Int.repr 1) tint)
                                          tuint) (tptr tuint)) tuint))
                                  (Ssequence
                                    (Sset _t'10
                                      (Efield
                                        (Ederef
                                          (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                          (Tstruct __CSRMatrix noattr)) _rows
                                        (tptr tuint)))
                                    (Ssequence
                                      (Sset _t'11
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'10 (tptr tuint))
                                            (Etempvar _j tuint) (tptr tuint))
                                          tuint))
                                      (Sset _rowCnt__1
                                        (Ebinop Osub (Etempvar _t'9 tuint)
                                          (Etempvar _t'11 tuint) tuint))))))
                              (Sifthenelse (Ebinop Olt (Etempvar _i__1 tuint)
                                             (Etempvar _rowCnt__1 tuint)
                                             tint)
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'6
                                      (Efield
                                        (Ederef
                                          (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                          (Tstruct __CSRMatrix noattr)) _rows
                                        (tptr tuint)))
                                    (Ssequence
                                      (Sset _t'7
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'6 (tptr tuint))
                                            (Etempvar _j tuint) (tptr tuint))
                                          tuint))
                                      (Sset _idx
                                        (Ebinop Oadd (Etempvar _t'7 tuint)
                                          (Etempvar _i__1 tuint) tuint))))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'5
                                        (Efield
                                          (Ederef
                                            (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                            (Tstruct __CSRMatrix noattr))
                                          _cols (tptr tuint)))
                                      (Sset _col
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'5 (tptr tuint))
                                            (Etempvar _idx tuint)
                                            (tptr tuint)) tuint)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'4
                                          (Efield
                                            (Ederef
                                              (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                              (Tstruct __CSRMatrix noattr))
                                            _values (tptr tfloat)))
                                        (Sset _value
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _t'4 (tptr tfloat))
                                              (Etempvar _idx tuint)
                                              (tptr tfloat)) tfloat)))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'3)
                                            (Evar _COOItem_malloc (Tfunction
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tfloat
                                                                    Tnil)))
                                                                    (tptr (Tstruct __COOItem noattr))
                                                                    cc_default))
                                            ((Etempvar _j tuint) ::
                                             (Etempvar _col tuint) ::
                                             (Etempvar _value tfloat) :: nil))
                                          (Sset _item
                                            (Etempvar _t'3 (tptr (Tstruct __COOItem noattr)))))
                                        (Scall None
                                          (Evar _COOChunk_push (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct __COOChunk noattr))
                                                                   (Tcons
                                                                    (tptr (Tstruct __COOItem noattr))
                                                                    Tnil))
                                                                 tvoid
                                                                 cc_default))
                                          ((Etempvar _chunk (tptr (Tstruct __COOChunk noattr))) ::
                                           (Etempvar _item (tptr (Tstruct __COOItem noattr))) ::
                                           nil))))))
                                Sskip)))
                          (Sset _j
                            (Ebinop Oadd (Etempvar _j tuint)
                              (Econst_int (Int.repr 1) tint) tuint)))))))
                (Sset _i__1
                  (Ebinop Oadd (Etempvar _i__1 tuint)
                    (Econst_int (Int.repr 1) tint) tuint))))
            (Sreturn (Some (Etempvar _chunks (tptr (tptr (Tstruct __COOChunk noattr))))))))))))
|}.

Definition f_swapHeap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_heap, (tptr (tptr (Tstruct __COOChunk noattr)))) ::
                (_i, tuint) :: (_j, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_temp, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'1, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _temp
    (Ederef
      (Ebinop Oadd (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
        (Etempvar _i tuint) (tptr (tptr (Tstruct __COOChunk noattr))))
      (tptr (Tstruct __COOChunk noattr))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Ederef
          (Ebinop Oadd
            (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
            (Etempvar _j tuint) (tptr (tptr (Tstruct __COOChunk noattr))))
          (tptr (Tstruct __COOChunk noattr))))
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
            (Etempvar _i tuint) (tptr (tptr (Tstruct __COOChunk noattr))))
          (tptr (Tstruct __COOChunk noattr)))
        (Etempvar _t'1 (tptr (Tstruct __COOChunk noattr)))))
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
          (Etempvar _j tuint) (tptr (tptr (Tstruct __COOChunk noattr))))
        (tptr (Tstruct __COOChunk noattr)))
      (Etempvar _temp (tptr (Tstruct __COOChunk noattr))))))
|}.

Definition f_addQueue := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_queue, (tptr (Tstruct __PriorQ noattr))) ::
                (_chunk, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_heap, (tptr (tptr (Tstruct __COOChunk noattr)))) ::
               (_idx, tuint) :: (_parent, tuint) :: (_t'7, tuint) ::
               (_t'6, tuint) :: (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, (tptr (Tstruct __COOChunk noattr))) :: (_t'2, tuint) ::
               (_t'1, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'6
      (Efield
        (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
          (Tstruct __PriorQ noattr)) _count tuint))
    (Ssequence
      (Sset _t'7
        (Efield
          (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
            (Tstruct __PriorQ noattr)) _maxCount tuint))
      (Sifthenelse (Ebinop Oge (Etempvar _t'6 tuint) (Etempvar _t'7 tuint)
                     tint)
        (Sreturn None)
        Sskip)))
  (Ssequence
    (Sset _heap
      (Efield
        (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
          (Tstruct __PriorQ noattr)) _heap
        (tptr (tptr (Tstruct __COOChunk noattr)))))
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
              (Tstruct __PriorQ noattr)) _count tuint))
        (Sassign
          (Efield
            (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
              (Tstruct __PriorQ noattr)) _count tuint)
          (Ebinop Oadd (Etempvar _t'5 tuint) (Econst_int (Int.repr 1) tint)
            tuint)))
      (Ssequence
        (Sset _idx
          (Efield
            (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
              (Tstruct __PriorQ noattr)) _count tuint))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                (Etempvar _idx tuint)
                (tptr (tptr (Tstruct __COOChunk noattr))))
              (tptr (Tstruct __COOChunk noattr)))
            (Etempvar _chunk (tptr (Tstruct __COOChunk noattr))))
          (Swhile
            (Ebinop Ogt (Etempvar _idx tuint) (Econst_int (Int.repr 1) tint)
              tint)
            (Ssequence
              (Sset _parent
                (Ebinop Odiv (Etempvar _idx tuint)
                  (Econst_int (Int.repr 2) tint) tuint))
              (Ssequence
                (Ssequence
                  (Sset _t'1
                    (Ederef
                      (Ebinop Oadd
                        (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                        (Etempvar _idx tuint)
                        (tptr (tptr (Tstruct __COOChunk noattr))))
                      (tptr (Tstruct __COOChunk noattr))))
                  (Ssequence
                    (Sset _t'2
                      (Efield
                        (Ederef
                          (Etempvar _t'1 (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _len tuint))
                    (Ssequence
                      (Sset _t'3
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                            (Etempvar _parent tuint)
                            (tptr (tptr (Tstruct __COOChunk noattr))))
                          (tptr (Tstruct __COOChunk noattr))))
                      (Ssequence
                        (Sset _t'4
                          (Efield
                            (Ederef
                              (Etempvar _t'3 (tptr (Tstruct __COOChunk noattr)))
                              (Tstruct __COOChunk noattr)) _len tuint))
                        (Sifthenelse (Ebinop Olt (Etempvar _t'2 tuint)
                                       (Etempvar _t'4 tuint) tint)
                          (Scall None
                            (Evar _swapHeap (Tfunction
                                              (Tcons
                                                (tptr (tptr (Tstruct __COOChunk noattr)))
                                                (Tcons tuint
                                                  (Tcons tuint Tnil))) tvoid
                                              cc_default))
                            ((Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr)))) ::
                             (Etempvar _idx tuint) ::
                             (Etempvar _parent tuint) :: nil))
                          Sskip)))))
                (Sset _idx (Etempvar _parent tuint))))))))))
|}.

Definition f_popQueue := {|
  fn_return := (tptr (Tstruct __COOChunk noattr));
  fn_callconv := cc_default;
  fn_params := ((_queue, (tptr (Tstruct __PriorQ noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_heap, (tptr (tptr (Tstruct __COOChunk noattr)))) ::
               (_result, (tptr (Tstruct __COOChunk noattr))) ::
               (_idx, tuint) :: (_count, tuint) :: (_leftIdx, tuint) ::
               (_rightIdx, tuint) :: (_t'23, tuint) :: (_t'22, tuint) ::
               (_t'21, tuint) :: (_t'20, tuint) ::
               (_t'19, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'18, tuint) ::
               (_t'17, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'16, tuint) ::
               (_t'15, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'14, tuint) ::
               (_t'13, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'12, tuint) ::
               (_t'11, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'10, tuint) ::
               (_t'9, (tptr (Tstruct __COOChunk noattr))) :: (_t'8, tuint) ::
               (_t'7, (tptr (Tstruct __COOChunk noattr))) :: (_t'6, tuint) ::
               (_t'5, (tptr (Tstruct __COOChunk noattr))) :: (_t'4, tuint) ::
               (_t'3, (tptr (Tstruct __COOChunk noattr))) :: (_t'2, tuint) ::
               (_t'1, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'23
      (Efield
        (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
          (Tstruct __PriorQ noattr)) _count tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'23 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
      Sskip))
  (Ssequence
    (Sset _heap
      (Efield
        (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
          (Tstruct __PriorQ noattr)) _heap
        (tptr (tptr (Tstruct __COOChunk noattr)))))
    (Ssequence
      (Sset _result
        (Ederef
          (Ebinop Oadd
            (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
            (Econst_int (Int.repr 1) tint)
            (tptr (tptr (Tstruct __COOChunk noattr))))
          (tptr (Tstruct __COOChunk noattr))))
      (Ssequence
        (Ssequence
          (Sset _t'22
            (Efield
              (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
                (Tstruct __PriorQ noattr)) _count tuint))
          (Scall None
            (Evar _swapHeap (Tfunction
                              (Tcons
                                (tptr (tptr (Tstruct __COOChunk noattr)))
                                (Tcons tuint (Tcons tuint Tnil))) tvoid
                              cc_default))
            ((Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr)))) ::
             (Econst_int (Int.repr 1) tint) :: (Etempvar _t'22 tuint) :: nil)))
        (Ssequence
          (Ssequence
            (Sset _t'21
              (Efield
                (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
                  (Tstruct __PriorQ noattr)) _count tuint))
            (Sassign
              (Efield
                (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
                  (Tstruct __PriorQ noattr)) _count tuint)
              (Ebinop Osub (Etempvar _t'21 tuint)
                (Econst_int (Int.repr 1) tint) tuint)))
          (Ssequence
            (Sset _idx (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Sset _count
                (Efield
                  (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
                    (Tstruct __PriorQ noattr)) _count tuint))
              (Ssequence
                (Swhile
                  (Ebinop Olt (Etempvar _idx tuint) (Etempvar _count tuint)
                    tint)
                  (Ssequence
                    (Sset _leftIdx
                      (Ebinop Omul (Etempvar _idx tuint)
                        (Econst_int (Int.repr 2) tint) tuint))
                    (Ssequence
                      (Sset _rightIdx
                        (Ebinop Oadd
                          (Ebinop Omul (Etempvar _idx tuint)
                            (Econst_int (Int.repr 2) tint) tuint)
                          (Econst_int (Int.repr 1) tint) tuint))
                      (Sifthenelse (Ebinop Olt (Etempvar _count tuint)
                                     (Etempvar _leftIdx tuint) tint)
                        Sbreak
                        (Sifthenelse (Ebinop Oeq (Etempvar _count tuint)
                                       (Etempvar _leftIdx tuint) tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'17
                                (Ederef
                                  (Ebinop Oadd
                                    (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                    (Etempvar _idx tuint)
                                    (tptr (tptr (Tstruct __COOChunk noattr))))
                                  (tptr (Tstruct __COOChunk noattr))))
                              (Ssequence
                                (Sset _t'18
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'17 (tptr (Tstruct __COOChunk noattr)))
                                      (Tstruct __COOChunk noattr)) _len
                                    tuint))
                                (Ssequence
                                  (Sset _t'19
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                        (Etempvar _leftIdx tuint)
                                        (tptr (tptr (Tstruct __COOChunk noattr))))
                                      (tptr (Tstruct __COOChunk noattr))))
                                  (Ssequence
                                    (Sset _t'20
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'19 (tptr (Tstruct __COOChunk noattr)))
                                          (Tstruct __COOChunk noattr)) _len
                                        tuint))
                                    (Sifthenelse (Ebinop Ogt
                                                   (Etempvar _t'18 tuint)
                                                   (Etempvar _t'20 tuint)
                                                   tint)
                                      (Scall None
                                        (Evar _swapHeap (Tfunction
                                                          (Tcons
                                                            (tptr (tptr (Tstruct __COOChunk noattr)))
                                                            (Tcons tuint
                                                              (Tcons tuint
                                                                Tnil))) tvoid
                                                          cc_default))
                                        ((Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr)))) ::
                                         (Etempvar _idx tuint) ::
                                         (Etempvar _leftIdx tuint) :: nil))
                                      Sskip)))))
                            (Sset _idx (Etempvar _leftIdx tuint)))
                          (Ssequence
                            (Sset _t'1
                              (Ederef
                                (Ebinop Oadd
                                  (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                  (Etempvar _idx tuint)
                                  (tptr (tptr (Tstruct __COOChunk noattr))))
                                (tptr (Tstruct __COOChunk noattr))))
                            (Ssequence
                              (Sset _t'2
                                (Efield
                                  (Ederef
                                    (Etempvar _t'1 (tptr (Tstruct __COOChunk noattr)))
                                    (Tstruct __COOChunk noattr)) _len tuint))
                              (Ssequence
                                (Sset _t'3
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                      (Etempvar _leftIdx tuint)
                                      (tptr (tptr (Tstruct __COOChunk noattr))))
                                    (tptr (Tstruct __COOChunk noattr))))
                                (Ssequence
                                  (Sset _t'4
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'3 (tptr (Tstruct __COOChunk noattr)))
                                        (Tstruct __COOChunk noattr)) _len
                                      tuint))
                                  (Sifthenelse (Ebinop Ogt
                                                 (Etempvar _t'2 tuint)
                                                 (Etempvar _t'4 tuint) tint)
                                    (Ssequence
                                      (Sset _t'9
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                            (Etempvar _idx tuint)
                                            (tptr (tptr (Tstruct __COOChunk noattr))))
                                          (tptr (Tstruct __COOChunk noattr))))
                                      (Ssequence
                                        (Sset _t'10
                                          (Efield
                                            (Ederef
                                              (Etempvar _t'9 (tptr (Tstruct __COOChunk noattr)))
                                              (Tstruct __COOChunk noattr))
                                            _len tuint))
                                        (Ssequence
                                          (Sset _t'11
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                                (Etempvar _rightIdx tuint)
                                                (tptr (tptr (Tstruct __COOChunk noattr))))
                                              (tptr (Tstruct __COOChunk noattr))))
                                          (Ssequence
                                            (Sset _t'12
                                              (Efield
                                                (Ederef
                                                  (Etempvar _t'11 (tptr (Tstruct __COOChunk noattr)))
                                                  (Tstruct __COOChunk noattr))
                                                _len tuint))
                                            (Sifthenelse (Ebinop Ogt
                                                           (Etempvar _t'10 tuint)
                                                           (Etempvar _t'12 tuint)
                                                           tint)
                                              (Ssequence
                                                (Sset _t'13
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                                      (Etempvar _leftIdx tuint)
                                                      (tptr (tptr (Tstruct __COOChunk noattr))))
                                                    (tptr (Tstruct __COOChunk noattr))))
                                                (Ssequence
                                                  (Sset _t'14
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _t'13 (tptr (Tstruct __COOChunk noattr)))
                                                        (Tstruct __COOChunk noattr))
                                                      _len tuint))
                                                  (Ssequence
                                                    (Sset _t'15
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                                          (Etempvar _rightIdx tuint)
                                                          (tptr (tptr (Tstruct __COOChunk noattr))))
                                                        (tptr (Tstruct __COOChunk noattr))))
                                                    (Ssequence
                                                      (Sset _t'16
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _t'15 (tptr (Tstruct __COOChunk noattr)))
                                                            (Tstruct __COOChunk noattr))
                                                          _len tuint))
                                                      (Sifthenelse (Ebinop Olt
                                                                    (Etempvar _t'14 tuint)
                                                                    (Etempvar _t'16 tuint)
                                                                    tint)
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _swapHeap 
                                                            (Tfunction
                                                              (Tcons
                                                                (tptr (tptr (Tstruct __COOChunk noattr)))
                                                                (Tcons tuint
                                                                  (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                              tvoid
                                                              cc_default))
                                                            ((Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr)))) ::
                                                             (Etempvar _idx tuint) ::
                                                             (Etempvar _leftIdx tuint) ::
                                                             nil))
                                                          (Sset _idx
                                                            (Etempvar _leftIdx tuint)))
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _swapHeap 
                                                            (Tfunction
                                                              (Tcons
                                                                (tptr (tptr (Tstruct __COOChunk noattr)))
                                                                (Tcons tuint
                                                                  (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                              tvoid
                                                              cc_default))
                                                            ((Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr)))) ::
                                                             (Etempvar _idx tuint) ::
                                                             (Etempvar _rightIdx tuint) ::
                                                             nil))
                                                          (Sset _idx
                                                            (Etempvar _rightIdx tuint))))))))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _swapHeap (Tfunction
                                                                    (Tcons
                                                                    (tptr (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                  ((Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr)))) ::
                                                   (Etempvar _idx tuint) ::
                                                   (Etempvar _leftIdx tuint) ::
                                                   nil))
                                                (Sset _idx
                                                  (Etempvar _leftIdx tuint))))))))
                                    (Ssequence
                                      (Sset _t'5
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                            (Etempvar _idx tuint)
                                            (tptr (tptr (Tstruct __COOChunk noattr))))
                                          (tptr (Tstruct __COOChunk noattr))))
                                      (Ssequence
                                        (Sset _t'6
                                          (Efield
                                            (Ederef
                                              (Etempvar _t'5 (tptr (Tstruct __COOChunk noattr)))
                                              (Tstruct __COOChunk noattr))
                                            _len tuint))
                                        (Ssequence
                                          (Sset _t'7
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                                (Etempvar _rightIdx tuint)
                                                (tptr (tptr (Tstruct __COOChunk noattr))))
                                              (tptr (Tstruct __COOChunk noattr))))
                                          (Ssequence
                                            (Sset _t'8
                                              (Efield
                                                (Ederef
                                                  (Etempvar _t'7 (tptr (Tstruct __COOChunk noattr)))
                                                  (Tstruct __COOChunk noattr))
                                                _len tuint))
                                            (Sifthenelse (Ebinop Ogt
                                                           (Etempvar _t'6 tuint)
                                                           (Etempvar _t'8 tuint)
                                                           tint)
                                              (Ssequence
                                                (Scall None
                                                  (Evar _swapHeap (Tfunction
                                                                    (Tcons
                                                                    (tptr (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                  ((Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr)))) ::
                                                   (Etempvar _idx tuint) ::
                                                   (Etempvar _rightIdx tuint) ::
                                                   nil))
                                                (Sset _idx
                                                  (Etempvar _rightIdx tuint)))
                                              Sbreak)))))))))))))))
                (Sreturn (Some (Etempvar _result (tptr (Tstruct __COOChunk noattr)))))))))))))
|}.

Definition f_COOItem_malloc := {|
  fn_return := (tptr (Tstruct __COOItem noattr));
  fn_callconv := cc_default;
  fn_params := ((_row, tuint) :: (_col, tuint) :: (_value, tfloat) :: nil);
  fn_vars := nil;
  fn_temps := ((_item, (tptr (Tstruct __COOItem noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct __COOItem noattr) tuint) :: nil))
    (Sset _item
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct __COOItem noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _item (tptr (Tstruct __COOItem noattr)))
          (Tstruct __COOItem noattr)) _row tuint) (Etempvar _row tuint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _item (tptr (Tstruct __COOItem noattr)))
            (Tstruct __COOItem noattr)) _col tuint) (Etempvar _col tuint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _item (tptr (Tstruct __COOItem noattr)))
              (Tstruct __COOItem noattr)) _value tfloat)
          (Etempvar _value tfloat))
        (Sreturn (Some (Etempvar _item (tptr (Tstruct __COOItem noattr)))))))))
|}.

Definition f_COOItem_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_item, (tptr (Tstruct __COOItem noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
  ((Etempvar _item (tptr (Tstruct __COOItem noattr))) :: nil))
|}.

Definition f_Matrix_malloc := {|
  fn_return := (tptr (Tstruct __Matrix noattr));
  fn_callconv := cc_default;
  fn_params := ((_height, tuint) :: (_width, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_matrix, (tptr (Tstruct __Matrix noattr))) ::
               (_values, (tptr tfloat)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Ebinop Omul
         (Ebinop Omul (Etempvar _height tuint) (Etempvar _width tuint) tuint)
         (Esizeof tfloat tuint) tuint) :: nil))
    (Sset _values (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tfloat))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
        ((Esizeof (Tstruct __Matrix noattr) tuint) :: nil))
      (Sset _matrix
        (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr (Tstruct __Matrix noattr)))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _matrix (tptr (Tstruct __Matrix noattr)))
            (Tstruct __Matrix noattr)) _height tuint)
        (Etempvar _height tuint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _matrix (tptr (Tstruct __Matrix noattr)))
              (Tstruct __Matrix noattr)) _width tuint)
          (Etempvar _width tuint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _matrix (tptr (Tstruct __Matrix noattr)))
                (Tstruct __Matrix noattr)) _values (tptr tfloat))
            (Etempvar _values (tptr tfloat)))
          (Sreturn (Some (Etempvar _matrix (tptr (Tstruct __Matrix noattr))))))))))
|}.

Definition f_Matrix_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_matrix, (tptr (Tstruct __Matrix noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tfloat)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _matrix (tptr (Tstruct __Matrix noattr)))
          (Tstruct __Matrix noattr)) _values (tptr tfloat)))
    (Scall None
      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _t'1 (tptr tfloat)) :: nil)))
  (Scall None
    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
    ((Etempvar _matrix (tptr (Tstruct __Matrix noattr))) :: nil)))
|}.

Definition f_Matrix_toCSR := {|
  fn_return := (tptr (Tstruct __CSRMatrix noattr));
  fn_callconv := cc_default;
  fn_params := ((_matrix, (tptr (Tstruct __Matrix noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_height, tuint) :: (_width, tuint) :: (_count, tuint) ::
               (_lenVal, tuint) :: (_i, tuint) ::
               (_csr, (tptr (Tstruct __CSRMatrix noattr))) ::
               (_index, tuint) :: (_i__1, tuint) :: (_j, tuint) ::
               (_offset, tuint) :: (_value, tfloat) ::
               (_t'1, (tptr (Tstruct __CSRMatrix noattr))) ::
               (_t'8, tfloat) :: (_t'7, (tptr tfloat)) ::
               (_t'6, (tptr tuint)) :: (_t'5, (tptr tfloat)) ::
               (_t'4, (tptr tfloat)) :: (_t'3, (tptr tuint)) ::
               (_t'2, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _height
    (Efield
      (Ederef (Etempvar _matrix (tptr (Tstruct __Matrix noattr)))
        (Tstruct __Matrix noattr)) _height tuint))
  (Ssequence
    (Sset _width
      (Efield
        (Ederef (Etempvar _matrix (tptr (Tstruct __Matrix noattr)))
          (Tstruct __Matrix noattr)) _width tuint))
    (Ssequence
      (Sset _count
        (Ebinop Omul (Etempvar _height tuint) (Etempvar _width tuint) tuint))
      (Ssequence
        (Sset _lenVal (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                               (Etempvar _count tuint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _t'7
                    (Efield
                      (Ederef
                        (Etempvar _matrix (tptr (Tstruct __Matrix noattr)))
                        (Tstruct __Matrix noattr)) _values (tptr tfloat)))
                  (Ssequence
                    (Sset _t'8
                      (Ederef
                        (Ebinop Oadd (Etempvar _t'7 (tptr tfloat))
                          (Etempvar _i tuint) (tptr tfloat)) tfloat))
                    (Sifthenelse (Ebinop One (Etempvar _t'8 tfloat)
                                   (Econst_float (Float.of_bits (Int64.repr 0)) tdouble)
                                   tint)
                      (Sset _lenVal
                        (Ebinop Oadd (Etempvar _lenVal tuint)
                          (Econst_int (Int.repr 1) tint) tuint))
                      Sskip))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tuint)
                  (Econst_int (Int.repr 1) tint) tuint))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _CSR_malloc (Tfunction
                                    (Tcons tuint
                                      (Tcons tuint (Tcons tuint Tnil)))
                                    (tptr (Tstruct __CSRMatrix noattr))
                                    cc_default))
                ((Etempvar _height tuint) :: (Etempvar _width tuint) ::
                 (Etempvar _lenVal tuint) :: nil))
              (Sset _csr (Etempvar _t'1 (tptr (Tstruct __CSRMatrix noattr)))))
            (Ssequence
              (Sset _index (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef
                        (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                        (Tstruct __CSRMatrix noattr)) _rows (tptr tuint)))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _t'6 (tptr tuint))
                        (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
                    (Econst_int (Int.repr 0) tint)))
                (Ssequence
                  (Ssequence
                    (Sset _i__1 (Econst_int (Int.repr 0) tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _i__1 tuint)
                                       (Etempvar _height tuint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Ssequence
                            (Sset _j (Econst_int (Int.repr 0) tint))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Olt (Etempvar _j tuint)
                                               (Etempvar _width tuint) tint)
                                  Sskip
                                  Sbreak)
                                (Ssequence
                                  (Sset _offset
                                    (Ebinop Oadd
                                      (Ebinop Omul (Etempvar _i__1 tuint)
                                        (Etempvar _width tuint) tuint)
                                      (Etempvar _j tuint) tuint))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'5
                                        (Efield
                                          (Ederef
                                            (Etempvar _matrix (tptr (Tstruct __Matrix noattr)))
                                            (Tstruct __Matrix noattr))
                                          _values (tptr tfloat)))
                                      (Sset _value
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'5 (tptr tfloat))
                                            (Etempvar _offset tuint)
                                            (tptr tfloat)) tfloat)))
                                    (Sifthenelse (Ebinop One
                                                   (Etempvar _value tfloat)
                                                   (Econst_float (Float.of_bits (Int64.repr 0)) tdouble)
                                                   tint)
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'4
                                            (Efield
                                              (Ederef
                                                (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                                (Tstruct __CSRMatrix noattr))
                                              _values (tptr tfloat)))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _t'4 (tptr tfloat))
                                                (Etempvar _index tuint)
                                                (tptr tfloat)) tfloat)
                                            (Etempvar _value tfloat)))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'3
                                              (Efield
                                                (Ederef
                                                  (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                                  (Tstruct __CSRMatrix noattr))
                                                _cols (tptr tuint)))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _t'3 (tptr tuint))
                                                  (Etempvar _index tuint)
                                                  (tptr tuint)) tuint)
                                              (Etempvar _j tuint)))
                                          (Sset _index
                                            (Ebinop Oadd
                                              (Etempvar _index tuint)
                                              (Econst_int (Int.repr 1) tint)
                                              tuint))))
                                      Sskip))))
                              (Sset _j
                                (Ebinop Oadd (Etempvar _j tuint)
                                  (Econst_int (Int.repr 1) tint) tuint))))
                          (Ssequence
                            (Sset _t'2
                              (Efield
                                (Ederef
                                  (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                  (Tstruct __CSRMatrix noattr)) _rows
                                (tptr tuint)))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Etempvar _t'2 (tptr tuint))
                                  (Ebinop Oadd (Etempvar _i__1 tuint)
                                    (Econst_int (Int.repr 1) tint) tuint)
                                  (tptr tuint)) tuint)
                              (Etempvar _index tuint)))))
                      (Sset _i__1
                        (Ebinop Oadd (Etempvar _i__1 tuint)
                          (Econst_int (Int.repr 1) tint) tuint))))
                  (Sreturn (Some (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr))))))))))))))
|}.

Definition f_CSR_malloc := {|
  fn_return := (tptr (Tstruct __CSRMatrix noattr));
  fn_callconv := cc_default;
  fn_params := ((_height, tuint) :: (_width, tuint) :: (_lenVal, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_csr, (tptr (Tstruct __CSRMatrix noattr))) ::
               (_cols, (tptr tuint)) :: (_rows, (tptr tuint)) ::
               (_values, (tptr tfloat)) :: (_t'4, (tptr tvoid)) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Ebinop Omul (Etempvar _lenVal tuint) (Esizeof tfloat tuint) tuint) ::
       nil))
    (Sset _values (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tfloat))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
        ((Ebinop Omul (Etempvar _lenVal tuint) (Esizeof tuint tuint) tuint) ::
         nil))
      (Sset _cols (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr tuint))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                          cc_default))
          ((Ebinop Omul
             (Ebinop Oadd (Etempvar _height tuint)
               (Econst_int (Int.repr 1) tint) tuint) (Esizeof tuint tuint)
             tuint) :: nil))
        (Sset _rows (Ecast (Etempvar _t'3 (tptr tvoid)) (tptr tuint))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                            cc_default))
            ((Esizeof (Tstruct __CSRMatrix noattr) tuint) :: nil))
          (Sset _csr
            (Ecast (Etempvar _t'4 (tptr tvoid))
              (tptr (Tstruct __CSRMatrix noattr)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                (Tstruct __CSRMatrix noattr)) _height tuint)
            (Etempvar _height tuint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                  (Tstruct __CSRMatrix noattr)) _width tuint)
              (Etempvar _width tuint))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                    (Tstruct __CSRMatrix noattr)) _lenVal tuint)
                (Etempvar _lenVal tuint))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                      (Tstruct __CSRMatrix noattr)) _values (tptr tfloat))
                  (Etempvar _values (tptr tfloat)))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                        (Tstruct __CSRMatrix noattr)) _cols (tptr tuint))
                    (Etempvar _cols (tptr tuint)))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                          (Tstruct __CSRMatrix noattr)) _rows (tptr tuint))
                      (Etempvar _rows (tptr tuint)))
                    (Sreturn (Some (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))))))))))))))
|}.

Definition f_CSR_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_csr, (tptr (Tstruct __CSRMatrix noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, (tptr tfloat)) :: (_t'2, (tptr tuint)) ::
               (_t'1, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3
      (Efield
        (Ederef (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
          (Tstruct __CSRMatrix noattr)) _values (tptr tfloat)))
    (Scall None
      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _t'3 (tptr tfloat)) :: nil)))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
            (Tstruct __CSRMatrix noattr)) _cols (tptr tuint)))
      (Scall None
        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Etempvar _t'2 (tptr tuint)) :: nil)))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
              (Tstruct __CSRMatrix noattr)) _rows (tptr tuint)))
        (Scall None
          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
          ((Etempvar _t'1 (tptr tuint)) :: nil)))
      (Scall None
        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Etempvar _csr (tptr (Tstruct __CSRMatrix noattr))) :: nil)))))
|}.

Definition f_CSR_dense := {|
  fn_return := (tptr (Tstruct __Matrix noattr));
  fn_callconv := cc_default;
  fn_params := ((_csr, (tptr (Tstruct __CSRMatrix noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_width, tuint) :: (_height, tuint) ::
               (_mat, (tptr (Tstruct __Matrix noattr))) :: (_count, tuint) ::
               (_i, tuint) :: (_i__1, tuint) :: (_rowStart, tuint) ::
               (_rowEnd, tuint) :: (_j, tuint) :: (_idx, tuint) ::
               (_t'1, (tptr (Tstruct __Matrix noattr))) ::
               (_t'9, (tptr tfloat)) :: (_t'8, (tptr tuint)) ::
               (_t'7, (tptr tuint)) :: (_t'6, tuint) ::
               (_t'5, (tptr tuint)) :: (_t'4, tfloat) ::
               (_t'3, (tptr tfloat)) :: (_t'2, (tptr tfloat)) :: nil);
  fn_body :=
(Ssequence
  (Sset _width
    (Efield
      (Ederef (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
        (Tstruct __CSRMatrix noattr)) _width tuint))
  (Ssequence
    (Sset _height
      (Efield
        (Ederef (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
          (Tstruct __CSRMatrix noattr)) _height tuint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _Matrix_malloc (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                 (tptr (Tstruct __Matrix noattr)) cc_default))
          ((Etempvar _height tuint) :: (Etempvar _width tuint) :: nil))
        (Sset _mat (Etempvar _t'1 (tptr (Tstruct __Matrix noattr)))))
      (Ssequence
        (Sset _count
          (Ebinop Omul (Etempvar _height tuint) (Etempvar _width tuint)
            tuint))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                               (Etempvar _count tuint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _t'9
                    (Efield
                      (Ederef
                        (Etempvar _mat (tptr (Tstruct __Matrix noattr)))
                        (Tstruct __Matrix noattr)) _values (tptr tfloat)))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _t'9 (tptr tfloat))
                        (Etempvar _i tuint) (tptr tfloat)) tfloat)
                    (Econst_int (Int.repr 0) tint))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tuint)
                  (Econst_int (Int.repr 1) tint) tuint))))
          (Ssequence
            (Ssequence
              (Sset _i__1 (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i__1 tuint)
                                 (Etempvar _height tuint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Ssequence
                      (Sset _t'8
                        (Efield
                          (Ederef
                            (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                            (Tstruct __CSRMatrix noattr)) _rows (tptr tuint)))
                      (Sset _rowStart
                        (Ederef
                          (Ebinop Oadd (Etempvar _t'8 (tptr tuint))
                            (Etempvar _i__1 tuint) (tptr tuint)) tuint)))
                    (Ssequence
                      (Ssequence
                        (Sset _t'7
                          (Efield
                            (Ederef
                              (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                              (Tstruct __CSRMatrix noattr)) _rows
                            (tptr tuint)))
                        (Sset _rowEnd
                          (Ederef
                            (Ebinop Oadd (Etempvar _t'7 (tptr tuint))
                              (Ebinop Oadd (Etempvar _i__1 tuint)
                                (Econst_int (Int.repr 1) tint) tuint)
                              (tptr tuint)) tuint)))
                      (Ssequence
                        (Sset _j (Etempvar _rowStart tuint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _j tuint)
                                           (Etempvar _rowEnd tuint) tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Ssequence
                                (Sset _t'5
                                  (Efield
                                    (Ederef
                                      (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                      (Tstruct __CSRMatrix noattr)) _cols
                                    (tptr tuint)))
                                (Ssequence
                                  (Sset _t'6
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _t'5 (tptr tuint))
                                        (Etempvar _j tuint) (tptr tuint))
                                      tuint))
                                  (Sset _idx
                                    (Ebinop Oadd
                                      (Ebinop Omul (Etempvar _i__1 tuint)
                                        (Etempvar _width tuint) tuint)
                                      (Etempvar _t'6 tuint) tuint))))
                              (Ssequence
                                (Sset _t'2
                                  (Efield
                                    (Ederef
                                      (Etempvar _mat (tptr (Tstruct __Matrix noattr)))
                                      (Tstruct __Matrix noattr)) _values
                                    (tptr tfloat)))
                                (Ssequence
                                  (Sset _t'3
                                    (Efield
                                      (Ederef
                                        (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                        (Tstruct __CSRMatrix noattr)) _values
                                      (tptr tfloat)))
                                  (Ssequence
                                    (Sset _t'4
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _t'3 (tptr tfloat))
                                          (Etempvar _j tuint) (tptr tfloat))
                                        tfloat))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _t'2 (tptr tfloat))
                                          (Etempvar _idx tuint)
                                          (tptr tfloat)) tfloat)
                                      (Etempvar _t'4 tfloat)))))))
                          (Sset _j
                            (Ebinop Oadd (Etempvar _j tuint)
                              (Econst_int (Int.repr 1) tint) tuint)))))))
                (Sset _i__1
                  (Ebinop Oadd (Etempvar _i__1 tuint)
                    (Econst_int (Int.repr 1) tint) tuint))))
            (Sreturn (Some (Etempvar _mat (tptr (Tstruct __Matrix noattr)))))))))))
|}.

Definition f_spgemm_sparch := {|
  fn_return := (tptr (Tstruct __CSRMatrix noattr));
  fn_callconv := cc_default;
  fn_params := ((_matA, (tptr (Tstruct __CSRMatrix noattr))) ::
                (_matB, (tptr (Tstruct __CSRMatrix noattr))) :: nil);
  fn_vars := ((_leftLen, tuint) :: (_pq, (Tstruct __PriorQ noattr)) ::
              (_treeItems, (tarray (tptr (Tstruct __COOChunk noattr)) 64)) ::
              nil);
  fn_temps := ((_leftChunk, (tptr (tptr (Tstruct __COOChunk noattr)))) ::
               (_multVal, (tptr (Tstruct __COOChunk noattr))) ::
               (_i, tuint) :: (_i__1, tuint) :: (_mergedIdx, tuint) ::
               (_kInit, tuint) ::
               (_mergedVal, (tptr (Tstruct __COOChunk noattr))) ::
               (_i__2, tuint) :: (_count, tuint) :: (_i__3, tuint) ::
               (_result, (tptr (Tstruct __COOChunk noattr))) ::
               (_csr, (tptr (Tstruct __CSRMatrix noattr))) ::
               (_node, (tptr (Tstruct __LLNode noattr))) ::
               (_next, (tptr (Tstruct __LLNode noattr))) :: (_i__4, tuint) ::
               (_t'11, (tptr (Tstruct __CSRMatrix noattr))) ::
               (_t'10, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'9, (tptr (Tstruct __COOChunk noattr))) :: (_t'8, tuint) ::
               (_t'7, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'6, (tptr tvoid)) :: (_t'5, tuint) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct __CSRMatrix noattr))) ::
               (_t'1, (tptr (tptr (Tstruct __COOChunk noattr)))) ::
               (_t'32, tuint) :: (_t'31, tuint) :: (_t'30, tuint) ::
               (_t'29, tuint) :: (_t'28, tuint) ::
               (_t'27, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'26, tuint) :: (_t'25, tuint) :: (_t'24, tuint) ::
               (_t'23, tuint) :: (_t'22, tuint) :: (_t'21, tuint) ::
               (_t'20, tuint) :: (_t'19, tuint) :: (_t'18, tuint) ::
               (_t'17, tuint) :: (_t'16, tuint) :: (_t'15, tuint) ::
               (_t'14, tuint) ::
               (_t'13, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'12, (tptr (tptr (Tstruct __COOChunk noattr)))) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _leftLen tuint) (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _condense (Tfunction
                          (Tcons (tptr (Tstruct __CSRMatrix noattr))
                            (Tcons (tptr tuint) Tnil))
                          (tptr (tptr (Tstruct __COOChunk noattr)))
                          cc_default))
        ((Etempvar _matA (tptr (Tstruct __CSRMatrix noattr))) ::
         (Eaddrof (Evar _leftLen tuint) (tptr tuint)) :: nil))
      (Sset _leftChunk
        (Etempvar _t'1 (tptr (tptr (Tstruct __COOChunk noattr))))))
    (Ssequence
      (Ssequence
        (Sset _t'30 (Evar _leftLen tuint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'30 tuint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Ssequence
            (Scall None
              (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default))
              ((Etempvar _leftChunk (tptr (tptr (Tstruct __COOChunk noattr)))) ::
               nil))
            (Ssequence
              (Ssequence
                (Sset _t'31
                  (Efield
                    (Ederef
                      (Etempvar _matA (tptr (Tstruct __CSRMatrix noattr)))
                      (Tstruct __CSRMatrix noattr)) _height tuint))
                (Ssequence
                  (Sset _t'32
                    (Efield
                      (Ederef
                        (Etempvar _matB (tptr (Tstruct __CSRMatrix noattr)))
                        (Tstruct __CSRMatrix noattr)) _width tuint))
                  (Scall (Some _t'2)
                    (Evar _CSR_malloc (Tfunction
                                        (Tcons tuint
                                          (Tcons tuint (Tcons tuint Tnil)))
                                        (tptr (Tstruct __CSRMatrix noattr))
                                        cc_default))
                    ((Etempvar _t'31 tuint) :: (Etempvar _t'32 tuint) ::
                     (Econst_int (Int.repr 0) tint) :: nil))))
              (Sreturn (Some (Etempvar _t'2 (tptr (Tstruct __CSRMatrix noattr)))))))
          Sskip))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'29 (Evar _leftLen tuint))
            (Scall (Some _t'3)
              (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                              cc_default))
              ((Ebinop Omul (Etempvar _t'29 tuint)
                 (Esizeof (Tstruct __COOChunk noattr) tuint) tuint) :: nil)))
          (Sset _multVal
            (Ecast (Etempvar _t'3 (tptr tvoid))
              (tptr (Tstruct __COOChunk noattr)))))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Ssequence
                  (Sset _t'28 (Evar _leftLen tuint))
                  (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                 (Etempvar _t'28 tuint) tint)
                    Sskip
                    Sbreak))
                (Ssequence
                  (Sset _t'27
                    (Ederef
                      (Ebinop Oadd
                        (Etempvar _leftChunk (tptr (tptr (Tstruct __COOChunk noattr))))
                        (Etempvar _i tuint)
                        (tptr (tptr (Tstruct __COOChunk noattr))))
                      (tptr (Tstruct __COOChunk noattr))))
                  (Scall None
                    (Evar _outerProd (Tfunction
                                       (Tcons
                                         (tptr (Tstruct __COOChunk noattr))
                                         (Tcons
                                           (tptr (Tstruct __CSRMatrix noattr))
                                           (Tcons
                                             (tptr (Tstruct __COOChunk noattr))
                                             Tnil))) tvoid cc_default))
                    ((Etempvar _t'27 (tptr (Tstruct __COOChunk noattr))) ::
                     (Etempvar _matB (tptr (Tstruct __CSRMatrix noattr))) ::
                     (Ebinop Oadd
                       (Etempvar _multVal (tptr (Tstruct __COOChunk noattr)))
                       (Etempvar _i tuint)
                       (tptr (Tstruct __COOChunk noattr))) :: nil))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tuint)
                  (Econst_int (Int.repr 1) tint) tuint))))
          (Ssequence
            (Sassign
              (Efield (Evar _pq (Tstruct __PriorQ noattr)) _count tuint)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Ssequence
                (Sset _t'26 (Evar _leftLen tuint))
                (Sassign
                  (Efield (Evar _pq (Tstruct __PriorQ noattr)) _maxCount
                    tuint) (Etempvar _t'26 tuint)))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'25 (Evar _leftLen tuint))
                    (Scall (Some _t'4)
                      (Evar _malloc (Tfunction (Tcons tuint Tnil)
                                      (tptr tvoid) cc_default))
                      ((Ebinop Omul
                         (Ebinop Oadd (Etempvar _t'25 tuint)
                           (Econst_int (Int.repr 1) tint) tuint)
                         (Esizeof (tptr (Tstruct __COOChunk noattr)) tuint)
                         tuint) :: nil)))
                  (Sassign
                    (Efield (Evar _pq (Tstruct __PriorQ noattr)) _heap
                      (tptr (tptr (Tstruct __COOChunk noattr))))
                    (Ecast (Etempvar _t'4 (tptr tvoid))
                      (tptr (tptr (Tstruct __COOChunk noattr))))))
                (Ssequence
                  (Ssequence
                    (Sset _i__1 (Econst_int (Int.repr 0) tint))
                    (Sloop
                      (Ssequence
                        (Ssequence
                          (Sset _t'24 (Evar _leftLen tuint))
                          (Sifthenelse (Ebinop Olt (Etempvar _i__1 tuint)
                                         (Etempvar _t'24 tuint) tint)
                            Sskip
                            Sbreak))
                        (Scall None
                          (Evar _addQueue (Tfunction
                                            (Tcons
                                              (tptr (Tstruct __PriorQ noattr))
                                              (Tcons
                                                (tptr (Tstruct __COOChunk noattr))
                                                Tnil)) tvoid cc_default))
                          ((Eaddrof (Evar _pq (Tstruct __PriorQ noattr))
                             (tptr (Tstruct __PriorQ noattr))) ::
                           (Ebinop Oadd
                             (Etempvar _multVal (tptr (Tstruct __COOChunk noattr)))
                             (Etempvar _i__1 tuint)
                             (tptr (Tstruct __COOChunk noattr))) :: nil)))
                      (Sset _i__1
                        (Ebinop Oadd (Etempvar _i__1 tuint)
                          (Econst_int (Int.repr 1) tint) tuint))))
                  (Ssequence
                    (Sset _mergedIdx (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'21 (Evar _leftLen tuint))
                          (Sifthenelse (Ebinop Oge (Etempvar _t'21 tuint)
                                         (Econst_int (Int.repr 2) tint) tint)
                            (Ssequence
                              (Sset _t'23 (Evar _leftLen tuint))
                              (Sset _t'5
                                (Ecast
                                  (Ebinop Oadd
                                    (Ebinop Omod
                                      (Ebinop Osub (Etempvar _t'23 tuint)
                                        (Econst_int (Int.repr 2) tint) tuint)
                                      (Ebinop Osub
                                        (Econst_int (Int.repr 64) tint)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      tuint) (Econst_int (Int.repr 2) tint)
                                    tuint) tuint)))
                            (Ssequence
                              (Sset _t'22 (Evar _leftLen tuint))
                              (Sset _t'5
                                (Ecast (Etempvar _t'22 tuint) tuint)))))
                        (Sset _kInit (Etempvar _t'5 tuint)))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'20 (Evar _leftLen tuint))
                            (Scall (Some _t'6)
                              (Evar _malloc (Tfunction (Tcons tuint Tnil)
                                              (tptr tvoid) cc_default))
                              ((Ebinop Omul
                                 (Ebinop Oadd
                                   (Ebinop Odiv (Etempvar _t'20 tuint)
                                     (Ebinop Osub
                                       (Econst_int (Int.repr 64) tint)
                                       (Econst_int (Int.repr 1) tint) tint)
                                     tuint) (Econst_int (Int.repr 1) tint)
                                   tuint)
                                 (Esizeof (Tstruct __COOChunk noattr) tuint)
                                 tuint) :: nil)))
                          (Sset _mergedVal
                            (Ecast (Etempvar _t'6 (tptr tvoid))
                              (tptr (Tstruct __COOChunk noattr)))))
                        (Ssequence
                          (Ssequence
                            (Sset _i__2 (Econst_int (Int.repr 0) tint))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Olt
                                               (Etempvar _i__2 tuint)
                                               (Etempvar _kInit tuint) tint)
                                  Sskip
                                  Sbreak)
                                (Ssequence
                                  (Scall (Some _t'7)
                                    (Evar _popQueue (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct __PriorQ noattr))
                                                        Tnil)
                                                      (tptr (Tstruct __COOChunk noattr))
                                                      cc_default))
                                    ((Eaddrof
                                       (Evar _pq (Tstruct __PriorQ noattr))
                                       (tptr (Tstruct __PriorQ noattr))) ::
                                     nil))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _treeItems (tarray (tptr (Tstruct __COOChunk noattr)) 64))
                                        (Etempvar _i__2 tuint)
                                        (tptr (tptr (Tstruct __COOChunk noattr))))
                                      (tptr (Tstruct __COOChunk noattr)))
                                    (Etempvar _t'7 (tptr (Tstruct __COOChunk noattr))))))
                              (Sset _i__2
                                (Ebinop Oadd (Etempvar _i__2 tuint)
                                  (Econst_int (Int.repr 1) tint) tuint))))
                          (Ssequence
                            (Scall None
                              (Evar _flattenByMergeTree (Tfunction
                                                          (Tcons
                                                            (tptr (tptr (Tstruct __COOChunk noattr)))
                                                            (Tcons tuint
                                                              (Tcons
                                                                (tptr (Tstruct __COOChunk noattr))
                                                                Tnil))) tvoid
                                                          cc_default))
                              ((Evar _treeItems (tarray (tptr (Tstruct __COOChunk noattr)) 64)) ::
                               (Etempvar _kInit tuint) ::
                               (Ebinop Oadd
                                 (Etempvar _mergedVal (tptr (Tstruct __COOChunk noattr)))
                                 (Econst_int (Int.repr 0) tint)
                                 (tptr (Tstruct __COOChunk noattr))) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _addQueue (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct __PriorQ noattr))
                                                    (Tcons
                                                      (tptr (Tstruct __COOChunk noattr))
                                                      Tnil)) tvoid
                                                  cc_default))
                                ((Eaddrof
                                   (Evar _pq (Tstruct __PriorQ noattr))
                                   (tptr (Tstruct __PriorQ noattr))) ::
                                 (Ebinop Oadd
                                   (Etempvar _mergedVal (tptr (Tstruct __COOChunk noattr)))
                                   (Econst_int (Int.repr 0) tint)
                                   (tptr (Tstruct __COOChunk noattr))) ::
                                 nil))
                              (Ssequence
                                (Sset _mergedIdx
                                  (Ebinop Oadd (Etempvar _mergedIdx tuint)
                                    (Econst_int (Int.repr 1) tint) tuint))
                                (Ssequence
                                  (Sloop
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'19
                                          (Efield
                                            (Evar _pq (Tstruct __PriorQ noattr))
                                            _count tuint))
                                        (Sifthenelse (Ebinop Ogt
                                                       (Etempvar _t'19 tuint)
                                                       (Econst_int (Int.repr 1) tint)
                                                       tint)
                                          Sskip
                                          Sbreak))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'17
                                              (Efield
                                                (Evar _pq (Tstruct __PriorQ noattr))
                                                _count tuint))
                                            (Sifthenelse (Ebinop Olt
                                                           (Etempvar _t'17 tuint)
                                                           (Econst_int (Int.repr 64) tint)
                                                           tint)
                                              (Ssequence
                                                (Sset _t'18
                                                  (Efield
                                                    (Evar _pq (Tstruct __PriorQ noattr))
                                                    _count tuint))
                                                (Sset _t'8
                                                  (Ecast
                                                    (Etempvar _t'18 tuint)
                                                    tuint)))
                                              (Sset _t'8
                                                (Ecast
                                                  (Econst_int (Int.repr 64) tint)
                                                  tuint))))
                                          (Sset _count (Etempvar _t'8 tuint)))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _i__3
                                              (Econst_int (Int.repr 0) tint))
                                            (Sloop
                                              (Ssequence
                                                (Sifthenelse (Ebinop Olt
                                                               (Etempvar _i__3 tuint)
                                                               (Etempvar _count tuint)
                                                               tint)
                                                  Sskip
                                                  Sbreak)
                                                (Ssequence
                                                  (Scall (Some _t'9)
                                                    (Evar _popQueue (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __PriorQ noattr))
                                                                    Tnil)
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    cc_default))
                                                    ((Eaddrof
                                                       (Evar _pq (Tstruct __PriorQ noattr))
                                                       (tptr (Tstruct __PriorQ noattr))) ::
                                                     nil))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _treeItems (tarray (tptr (Tstruct __COOChunk noattr)) 64))
                                                        (Etempvar _i__3 tuint)
                                                        (tptr (tptr (Tstruct __COOChunk noattr))))
                                                      (tptr (Tstruct __COOChunk noattr)))
                                                    (Etempvar _t'9 (tptr (Tstruct __COOChunk noattr))))))
                                              (Sset _i__3
                                                (Ebinop Oadd
                                                  (Etempvar _i__3 tuint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tuint))))
                                          (Ssequence
                                            (Scall None
                                              (Evar _flattenByMergeTree 
                                              (Tfunction
                                                (Tcons
                                                  (tptr (tptr (Tstruct __COOChunk noattr)))
                                                  (Tcons tuint
                                                    (Tcons
                                                      (tptr (Tstruct __COOChunk noattr))
                                                      Tnil))) tvoid
                                                cc_default))
                                              ((Evar _treeItems (tarray (tptr (Tstruct __COOChunk noattr)) 64)) ::
                                               (Etempvar _count tuint) ::
                                               (Ebinop Oadd
                                                 (Etempvar _mergedVal (tptr (Tstruct __COOChunk noattr)))
                                                 (Etempvar _mergedIdx tuint)
                                                 (tptr (Tstruct __COOChunk noattr))) ::
                                               nil))
                                            (Ssequence
                                              (Scall None
                                                (Evar _addQueue (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct __PriorQ noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    Tnil))
                                                                  tvoid
                                                                  cc_default))
                                                ((Eaddrof
                                                   (Evar _pq (Tstruct __PriorQ noattr))
                                                   (tptr (Tstruct __PriorQ noattr))) ::
                                                 (Ebinop Oadd
                                                   (Etempvar _mergedVal (tptr (Tstruct __COOChunk noattr)))
                                                   (Etempvar _mergedIdx tuint)
                                                   (tptr (Tstruct __COOChunk noattr))) ::
                                                 nil))
                                              (Sset _mergedIdx
                                                (Ebinop Oadd
                                                  (Etempvar _mergedIdx tuint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tuint)))))))
                                    Sskip)
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'10)
                                        (Evar _popQueue (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct __PriorQ noattr))
                                                            Tnil)
                                                          (tptr (Tstruct __COOChunk noattr))
                                                          cc_default))
                                        ((Eaddrof
                                           (Evar _pq (Tstruct __PriorQ noattr))
                                           (tptr (Tstruct __PriorQ noattr))) ::
                                         nil))
                                      (Sset _result
                                        (Etempvar _t'10 (tptr (Tstruct __COOChunk noattr)))))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'15
                                            (Efield
                                              (Ederef
                                                (Etempvar _matA (tptr (Tstruct __CSRMatrix noattr)))
                                                (Tstruct __CSRMatrix noattr))
                                              _height tuint))
                                          (Ssequence
                                            (Sset _t'16
                                              (Efield
                                                (Ederef
                                                  (Etempvar _matB (tptr (Tstruct __CSRMatrix noattr)))
                                                  (Tstruct __CSRMatrix noattr))
                                                _width tuint))
                                            (Scall (Some _t'11)
                                              (Evar _COOChunk_toCSR (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                    (tptr (Tstruct __CSRMatrix noattr))
                                                                    cc_default))
                                              ((Etempvar _result (tptr (Tstruct __COOChunk noattr))) ::
                                               (Etempvar _t'15 tuint) ::
                                               (Etempvar _t'16 tuint) :: nil))))
                                        (Sset _csr
                                          (Etempvar _t'11 (tptr (Tstruct __CSRMatrix noattr)))))
                                      (Ssequence
                                        (Sset _node
                                          (Efield
                                            (Ederef
                                              (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                                              (Tstruct __COOChunk noattr))
                                            _head
                                            (tptr (Tstruct __LLNode noattr))))
                                        (Ssequence
                                          (Swhile
                                            (Etempvar _node (tptr (Tstruct __LLNode noattr)))
                                            (Ssequence
                                              (Sset _next
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _node (tptr (Tstruct __LLNode noattr)))
                                                    (Tstruct __LLNode noattr))
                                                  _next
                                                  (tptr (Tstruct __LLNode noattr))))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _LLNode_freeAll 
                                                  (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct __LLNode noattr))
                                                      Tnil) tvoid cc_default))
                                                  ((Etempvar _node (tptr (Tstruct __LLNode noattr))) ::
                                                   nil))
                                                (Sset _node
                                                  (Etempvar _next (tptr (Tstruct __LLNode noattr)))))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _i__4
                                                (Econst_int (Int.repr 0) tint))
                                              (Sloop
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'14
                                                      (Evar _leftLen tuint))
                                                    (Sifthenelse (Ebinop Olt
                                                                   (Etempvar _i__4 tuint)
                                                                   (Etempvar _t'14 tuint)
                                                                   tint)
                                                      Sskip
                                                      Sbreak))
                                                  (Ssequence
                                                    (Sset _t'13
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _leftChunk (tptr (tptr (Tstruct __COOChunk noattr))))
                                                          (Etempvar _i__4 tuint)
                                                          (tptr (tptr (Tstruct __COOChunk noattr))))
                                                        (tptr (Tstruct __COOChunk noattr))))
                                                    (Scall None
                                                      (Evar _COOChunk_freeAll 
                                                      (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct __COOChunk noattr))
                                                          Tnil) tvoid
                                                        cc_default))
                                                      ((Etempvar _t'13 (tptr (Tstruct __COOChunk noattr))) ::
                                                       nil))))
                                                (Sset _i__4
                                                  (Ebinop Oadd
                                                    (Etempvar _i__4 tuint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tuint))))
                                            (Ssequence
                                              (Scall None
                                                (Evar _free (Tfunction
                                                              (Tcons
                                                                (tptr tvoid)
                                                                Tnil) tvoid
                                                              cc_default))
                                                ((Etempvar _leftChunk (tptr (tptr (Tstruct __COOChunk noattr)))) ::
                                                 nil))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'12
                                                    (Efield
                                                      (Evar _pq (Tstruct __PriorQ noattr))
                                                      _heap
                                                      (tptr (tptr (Tstruct __COOChunk noattr)))))
                                                  (Scall None
                                                    (Evar _free (Tfunction
                                                                  (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                  tvoid
                                                                  cc_default))
                                                    ((Etempvar _t'12 (tptr (tptr (Tstruct __COOChunk noattr)))) ::
                                                     nil)))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _free (Tfunction
                                                                  (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                  tvoid
                                                                  cc_default))
                                                    ((Etempvar _mergedVal (tptr (Tstruct __COOChunk noattr))) ::
                                                     nil))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _free (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)
                                                                    tvoid
                                                                    cc_default))
                                                      ((Etempvar _multVal (tptr (Tstruct __COOChunk noattr))) ::
                                                       nil))
                                                    (Sreturn (Some (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))))))))))))))))))))))))))))))
|}.

Definition f_gemm_sparch := {|
  fn_return := (tptr (Tstruct __Matrix noattr));
  fn_callconv := cc_default;
  fn_params := ((_matA, (tptr (Tstruct __Matrix noattr))) ::
                (_matB, (tptr (Tstruct __Matrix noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_left, (tptr (Tstruct __CSRMatrix noattr))) ::
               (_right, (tptr (Tstruct __CSRMatrix noattr))) ::
               (_mm, (tptr (Tstruct __CSRMatrix noattr))) ::
               (_result, (tptr (Tstruct __Matrix noattr))) ::
               (_t'4, (tptr (Tstruct __Matrix noattr))) ::
               (_t'3, (tptr (Tstruct __CSRMatrix noattr))) ::
               (_t'2, (tptr (Tstruct __CSRMatrix noattr))) ::
               (_t'1, (tptr (Tstruct __CSRMatrix noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _Matrix_toCSR (Tfunction
                            (Tcons (tptr (Tstruct __Matrix noattr)) Tnil)
                            (tptr (Tstruct __CSRMatrix noattr)) cc_default))
      ((Etempvar _matA (tptr (Tstruct __Matrix noattr))) :: nil))
    (Sset _left (Etempvar _t'1 (tptr (Tstruct __CSRMatrix noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _Matrix_toCSR (Tfunction
                              (Tcons (tptr (Tstruct __Matrix noattr)) Tnil)
                              (tptr (Tstruct __CSRMatrix noattr)) cc_default))
        ((Etempvar _matB (tptr (Tstruct __Matrix noattr))) :: nil))
      (Sset _right (Etempvar _t'2 (tptr (Tstruct __CSRMatrix noattr)))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _spgemm_sparch (Tfunction
                                 (Tcons (tptr (Tstruct __CSRMatrix noattr))
                                   (Tcons (tptr (Tstruct __CSRMatrix noattr))
                                     Tnil))
                                 (tptr (Tstruct __CSRMatrix noattr))
                                 cc_default))
          ((Etempvar _left (tptr (Tstruct __CSRMatrix noattr))) ::
           (Etempvar _right (tptr (Tstruct __CSRMatrix noattr))) :: nil))
        (Sset _mm (Etempvar _t'3 (tptr (Tstruct __CSRMatrix noattr)))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _CSR_dense (Tfunction
                               (Tcons (tptr (Tstruct __CSRMatrix noattr))
                                 Tnil) (tptr (Tstruct __Matrix noattr))
                               cc_default))
            ((Etempvar _mm (tptr (Tstruct __CSRMatrix noattr))) :: nil))
          (Sset _result (Etempvar _t'4 (tptr (Tstruct __Matrix noattr)))))
        (Ssequence
          (Scall None
            (Evar _CSR_free (Tfunction
                              (Tcons (tptr (Tstruct __CSRMatrix noattr))
                                Tnil) tvoid cc_default))
            ((Etempvar _mm (tptr (Tstruct __CSRMatrix noattr))) :: nil))
          (Ssequence
            (Scall None
              (Evar _CSR_free (Tfunction
                                (Tcons (tptr (Tstruct __CSRMatrix noattr))
                                  Tnil) tvoid cc_default))
              ((Etempvar _right (tptr (Tstruct __CSRMatrix noattr))) :: nil))
            (Ssequence
              (Scall None
                (Evar _CSR_free (Tfunction
                                  (Tcons (tptr (Tstruct __CSRMatrix noattr))
                                    Tnil) tvoid cc_default))
                ((Etempvar _left (tptr (Tstruct __CSRMatrix noattr))) :: nil))
              (Sreturn (Some (Etempvar _result (tptr (Tstruct __Matrix noattr))))))))))))
|}.

Definition f_matmul := {|
  fn_return := (tptr (Tstruct __Matrix noattr));
  fn_callconv := cc_default;
  fn_params := ((_matA, (tptr (Tstruct __Matrix noattr))) ::
                (_matB, (tptr (Tstruct __Matrix noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_result, (tptr (Tstruct __Matrix noattr))) ::
               (_height, tuint) :: (_width, tuint) :: (_iterLen, tuint) ::
               (_i, tuint) :: (_j, tuint) :: (_idx, tuint) :: (_ai, tuint) ::
               (_bi, tuint) :: (_k, tuint) ::
               (_t'1, (tptr (Tstruct __Matrix noattr))) :: (_t'13, tuint) ::
               (_t'12, tuint) :: (_t'11, tuint) :: (_t'10, tuint) ::
               (_t'9, (tptr tfloat)) :: (_t'8, tfloat) ::
               (_t'7, (tptr tfloat)) :: (_t'6, tfloat) ::
               (_t'5, (tptr tfloat)) :: (_t'4, tfloat) ::
               (_t'3, (tptr tfloat)) :: (_t'2, (tptr tfloat)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'12
      (Efield
        (Ederef (Etempvar _matA (tptr (Tstruct __Matrix noattr)))
          (Tstruct __Matrix noattr)) _width tuint))
    (Ssequence
      (Sset _t'13
        (Efield
          (Ederef (Etempvar _matB (tptr (Tstruct __Matrix noattr)))
            (Tstruct __Matrix noattr)) _height tuint))
      (Sifthenelse (Ebinop One (Etempvar _t'12 tuint) (Etempvar _t'13 tuint)
                     tint)
        (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
        Sskip)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'10
          (Efield
            (Ederef (Etempvar _matA (tptr (Tstruct __Matrix noattr)))
              (Tstruct __Matrix noattr)) _height tuint))
        (Ssequence
          (Sset _t'11
            (Efield
              (Ederef (Etempvar _matB (tptr (Tstruct __Matrix noattr)))
                (Tstruct __Matrix noattr)) _width tuint))
          (Scall (Some _t'1)
            (Evar _Matrix_malloc (Tfunction (Tcons tuint (Tcons tuint Tnil))
                                   (tptr (Tstruct __Matrix noattr))
                                   cc_default))
            ((Etempvar _t'10 tuint) :: (Etempvar _t'11 tuint) :: nil))))
      (Sset _result (Etempvar _t'1 (tptr (Tstruct __Matrix noattr)))))
    (Ssequence
      (Sset _height
        (Efield
          (Ederef (Etempvar _matA (tptr (Tstruct __Matrix noattr)))
            (Tstruct __Matrix noattr)) _height tuint))
      (Ssequence
        (Sset _width
          (Efield
            (Ederef (Etempvar _matB (tptr (Tstruct __Matrix noattr)))
              (Tstruct __Matrix noattr)) _width tuint))
        (Ssequence
          (Sset _iterLen
            (Efield
              (Ederef (Etempvar _matA (tptr (Tstruct __Matrix noattr)))
                (Tstruct __Matrix noattr)) _width tuint))
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                 (Etempvar _height tuint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _j (Econst_int (Int.repr 0) tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _j tuint)
                                       (Etempvar _width tuint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Sset _idx
                            (Ebinop Oadd
                              (Ebinop Omul (Etempvar _width tuint)
                                (Etempvar _i tuint) tuint)
                              (Etempvar _j tuint) tuint))
                          (Ssequence
                            (Sset _ai
                              (Ebinop Omul (Etempvar _iterLen tuint)
                                (Etempvar _i tuint) tuint))
                            (Ssequence
                              (Sset _bi (Etempvar _j tuint))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'9
                                    (Efield
                                      (Ederef
                                        (Etempvar _result (tptr (Tstruct __Matrix noattr)))
                                        (Tstruct __Matrix noattr)) _values
                                      (tptr tfloat)))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _t'9 (tptr tfloat))
                                        (Etempvar _idx tuint) (tptr tfloat))
                                      tfloat) (Econst_int (Int.repr 0) tint)))
                                (Ssequence
                                  (Sset _k (Econst_int (Int.repr 0) tint))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _k tuint)
                                                     (Etempvar _iterLen tuint)
                                                     tint)
                                        Sskip
                                        Sbreak)
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'2
                                            (Efield
                                              (Ederef
                                                (Etempvar _result (tptr (Tstruct __Matrix noattr)))
                                                (Tstruct __Matrix noattr))
                                              _values (tptr tfloat)))
                                          (Ssequence
                                            (Sset _t'3
                                              (Efield
                                                (Ederef
                                                  (Etempvar _result (tptr (Tstruct __Matrix noattr)))
                                                  (Tstruct __Matrix noattr))
                                                _values (tptr tfloat)))
                                            (Ssequence
                                              (Sset _t'4
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _t'3 (tptr tfloat))
                                                    (Etempvar _idx tuint)
                                                    (tptr tfloat)) tfloat))
                                              (Ssequence
                                                (Sset _t'5
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _matA (tptr (Tstruct __Matrix noattr)))
                                                      (Tstruct __Matrix noattr))
                                                    _values (tptr tfloat)))
                                                (Ssequence
                                                  (Sset _t'6
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _t'5 (tptr tfloat))
                                                        (Etempvar _ai tuint)
                                                        (tptr tfloat))
                                                      tfloat))
                                                  (Ssequence
                                                    (Sset _t'7
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _matB (tptr (Tstruct __Matrix noattr)))
                                                          (Tstruct __Matrix noattr))
                                                        _values
                                                        (tptr tfloat)))
                                                    (Ssequence
                                                      (Sset _t'8
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Etempvar _t'7 (tptr tfloat))
                                                            (Etempvar _bi tuint)
                                                            (tptr tfloat))
                                                          tfloat))
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Etempvar _t'2 (tptr tfloat))
                                                            (Etempvar _idx tuint)
                                                            (tptr tfloat))
                                                          tfloat)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'4 tfloat)
                                                          (Ebinop Omul
                                                            (Etempvar _t'6 tfloat)
                                                            (Etempvar _t'8 tfloat)
                                                            tfloat) tfloat)))))))))
                                        (Ssequence
                                          (Sset _ai
                                            (Ebinop Oadd (Etempvar _ai tuint)
                                              (Econst_int (Int.repr 1) tint)
                                              tuint))
                                          (Sset _bi
                                            (Ebinop Oadd (Etempvar _bi tuint)
                                              (Etempvar _width tuint) tuint)))))
                                    (Sset _k
                                      (Ebinop Oadd (Etempvar _k tuint)
                                        (Econst_int (Int.repr 1) tint) tuint)))))))))
                      (Sset _j
                        (Ebinop Oadd (Etempvar _j tuint)
                          (Econst_int (Int.repr 1) tint) tuint)))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tuint)
                    (Econst_int (Int.repr 1) tint) tuint))))
            (Sreturn (Some (Etempvar _result (tptr (Tstruct __Matrix noattr)))))))))))
|}.

Definition composites : list composite_definition :=
(Composite __Matrix Struct
   ((_height, tuint) :: (_width, tuint) :: (_values, (tptr tfloat)) :: nil)
   noattr ::
 Composite __COOItem Struct
   ((_row, tuint) :: (_col, tuint) :: (_value, tfloat) :: nil)
   noattr ::
 Composite __CSRMatrix Struct
   ((_height, tuint) :: (_width, tuint) :: (_lenVal, tuint) ::
    (_values, (tptr tfloat)) :: (_cols, (tptr tuint)) ::
    (_rows, (tptr tuint)) :: nil)
   noattr ::
 Composite __LLNode Struct
   ((_item, (tptr (Tstruct __COOItem noattr))) ::
    (_next, (tptr (Tstruct __LLNode noattr))) :: nil)
   noattr ::
 Composite __COOChunk Struct
   ((_len, tuint) :: (_head, (tptr (Tstruct __LLNode noattr))) ::
    (_tail, (tptr (Tstruct __LLNode noattr))) :: nil)
   noattr ::
 Composite __PriorQ Struct
   ((_count, tuint) :: (_maxCount, tuint) ::
    (_heap, (tptr (tptr (Tstruct __COOChunk noattr)))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tint :: nil) AST.Tint
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_LLNode_malloc, Gfun(Internal f_LLNode_malloc)) ::
 (_LLNode_free, Gfun(Internal f_LLNode_free)) ::
 (_LLNode_freeAll, Gfun(Internal f_LLNode_freeAll)) ::
 (_COOChunk_malloc, Gfun(Internal f_COOChunk_malloc)) ::
 (_COOChunk_free, Gfun(Internal f_COOChunk_free)) ::
 (_COOChunk_freeNodes, Gfun(Internal f_COOChunk_freeNodes)) ::
 (_COOChunk_freeAll, Gfun(Internal f_COOChunk_freeAll)) ::
 (_COOChunk_push, Gfun(Internal f_COOChunk_push)) ::
 (_COOChunk_append, Gfun(Internal f_COOChunk_append)) ::
 (_COOChunk_concat, Gfun(Internal f_COOChunk_concat)) ::
 (_COOChunk_toCSR, Gfun(Internal f_COOChunk_toCSR)) ::
 (_COOChunk_print, Gfun(Internal f_COOChunk_print)) ::
 (_outerProd, Gfun(Internal f_outerProd)) ::
 (_posCmp, Gfun(Internal f_posCmp)) ::
 (_mergeLow, Gfun(Internal f_mergeLow)) ::
 (_mergeTop, Gfun(Internal f_mergeTop)) ::
 (_elimZero, Gfun(Internal f_elimZero)) ::
 (_mergeHier, Gfun(Internal f_mergeHier)) ::
 (_merge, Gfun(Internal f_merge)) ::
 (_flattenByMergeTree, Gfun(Internal f_flattenByMergeTree)) ::
 (_condense, Gfun(Internal f_condense)) ::
 (_swapHeap, Gfun(Internal f_swapHeap)) ::
 (_addQueue, Gfun(Internal f_addQueue)) ::
 (_popQueue, Gfun(Internal f_popQueue)) ::
 (_COOItem_malloc, Gfun(Internal f_COOItem_malloc)) ::
 (_COOItem_free, Gfun(Internal f_COOItem_free)) ::
 (_Matrix_malloc, Gfun(Internal f_Matrix_malloc)) ::
 (_Matrix_free, Gfun(Internal f_Matrix_free)) ::
 (_Matrix_toCSR, Gfun(Internal f_Matrix_toCSR)) ::
 (_CSR_malloc, Gfun(Internal f_CSR_malloc)) ::
 (_CSR_free, Gfun(Internal f_CSR_free)) ::
 (_CSR_dense, Gfun(Internal f_CSR_dense)) ::
 (_spgemm_sparch, Gfun(Internal f_spgemm_sparch)) ::
 (_gemm_sparch, Gfun(Internal f_gemm_sparch)) ::
 (_matmul, Gfun(Internal f_matmul)) :: nil).

Definition public_idents : list ident :=
(_matmul :: _gemm_sparch :: _spgemm_sparch :: _CSR_dense :: _CSR_free ::
 _CSR_malloc :: _Matrix_toCSR :: _Matrix_free :: _Matrix_malloc ::
 _COOItem_free :: _COOItem_malloc :: _popQueue :: _addQueue :: _swapHeap ::
 _condense :: _flattenByMergeTree :: _merge :: _mergeHier :: _elimZero ::
 _mergeTop :: _mergeLow :: _posCmp :: _outerProd :: _COOChunk_print ::
 _COOChunk_toCSR :: _COOChunk_concat :: _COOChunk_append :: _COOChunk_push ::
 _COOChunk_freeAll :: _COOChunk_freeNodes :: _COOChunk_free ::
 _COOChunk_malloc :: _LLNode_freeAll :: _LLNode_free :: _LLNode_malloc ::
 _free :: _malloc :: _printf :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


