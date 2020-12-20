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
  Definition normalized := false.
End Info.

Definition _COOChunk_append : ident := $"COOChunk_append".
Definition _COOChunk_free : ident := $"COOChunk_free".
Definition _COOChunk_freeAll : ident := $"COOChunk_freeAll".
Definition _COOChunk_malloc : ident := $"COOChunk_malloc".
Definition _COOChunk_push : ident := $"COOChunk_push".
Definition _COOChunk_toCSR : ident := $"COOChunk_toCSR".
Definition _COOItem_free : ident := $"COOItem_free".
Definition _COOItem_malloc : ident := $"COOItem_malloc".
Definition _CSR_dense : ident := $"CSR_dense".
Definition _CSR_free : ident := $"CSR_free".
Definition _CSR_malloc : ident := $"CSR_malloc".
Definition _LLNode_free : ident := $"LLNode_free".
Definition _LLNode_freeAll : ident := $"LLNode_freeAll".
Definition _LLNode_malloc : ident := $"LLNode_malloc".
Definition _Matrix_free : ident := $"Matrix_free".
Definition _Matrix_malloc : ident := $"Matrix_malloc".
Definition _Matrix_toCSR : ident := $"Matrix_toCSR".
Definition __COOChunk : ident := $"_COOChunk".
Definition __COOItem : ident := $"_COOItem".
Definition __CSRMatrix : ident := $"_CSRMatrix".
Definition __LLNode : ident := $"_LLNode".
Definition __Matrix : ident := $"_Matrix".
Definition __PriorQ : ident := $"_PriorQ".
Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _addQueue : ident := $"addQueue".
Definition _chunk : ident := $"chunk".
Definition _chunks : ident := $"chunks".
Definition _col : ident := $"col".
Definition _colHead : ident := $"colHead".
Definition _cols : ident := $"cols".
Definition _condense : ident := $"condense".
Definition _count : ident := $"count".
Definition _csr : ident := $"csr".
Definition _currLen : ident := $"currLen".
Definition _elimZero : ident := $"elimZero".
Definition _flattenByMergeTree : ident := $"flattenByMergeTree".
Definition _free : ident := $"free".
Definition _gemm_sparch : ident := $"gemm_sparch".
Definition _head : ident := $"head".
Definition _heap : ident := $"heap".
Definition _height : ident := $"height".
Definition _i : ident := $"i".
Definition _i__1 : ident := $"i__1".
Definition _i__2 : ident := $"i__2".
Definition _i__3 : ident := $"i__3".
Definition _i__4 : ident := $"i__4".
Definition _idx : ident := $"idx".
Definition _index : ident := $"index".
Definition _item : ident := $"item".
Definition _j : ident := $"j".
Definition _kInit : ident := $"kInit".
Definition _left : ident := $"left".
Definition _leftChunk : ident := $"leftChunk".
Definition _leftIdx : ident := $"leftIdx".
Definition _leftLen : ident := $"leftLen".
Definition _leftVal : ident := $"leftVal".
Definition _len : ident := $"len".
Definition _lenVal : ident := $"lenVal".
Definition _li : ident := $"li".
Definition _litem : ident := $"litem".
Definition _main : ident := $"main".
Definition _malloc : ident := $"malloc".
Definition _mat : ident := $"mat".
Definition _matA : ident := $"matA".
Definition _matB : ident := $"matB".
Definition _matrix : ident := $"matrix".
Definition _maxBound : ident := $"maxBound".
Definition _maxCount : ident := $"maxCount".
Definition _merge : ident := $"merge".
Definition _mergeLow : ident := $"mergeLow".
Definition _mergeTop : ident := $"mergeTop".
Definition _mergedIdx : ident := $"mergedIdx".
Definition _mergedVal : ident := $"mergedVal".
Definition _merger : ident := $"merger".
Definition _mm : ident := $"mm".
Definition _multVal : ident := $"multVal".
Definition _newItem : ident := $"newItem".
Definition _next : ident := $"next".
Definition _nextLen : ident := $"nextLen".
Definition _node : ident := $"node".
Definition _offset : ident := $"offset".
Definition _outLen : ident := $"outLen".
Definition _outerProd : ident := $"outerProd".
Definition _parent : ident := $"parent".
Definition _popQueue : ident := $"popQueue".
Definition _pq : ident := $"pq".
Definition _queue : ident := $"queue".
Definition _result : ident := $"result".
Definition _ri : ident := $"ri".
Definition _right : ident := $"right".
Definition _rightIdx : ident := $"rightIdx".
Definition _rightRowEnd : ident := $"rightRowEnd".
Definition _rightRowStart : ident := $"rightRowStart".
Definition _rightVal : ident := $"rightVal".
Definition _ritem : ident := $"ritem".
Definition _row : ident := $"row".
Definition _rowCnt : ident := $"rowCnt".
Definition _rowCnt__1 : ident := $"rowCnt__1".
Definition _rowEnd : ident := $"rowEnd".
Definition _rowId : ident := $"rowId".
Definition _rowStart : ident := $"rowStart".
Definition _rows : ident := $"rows".
Definition _spgemm_sparch : ident := $"spgemm_sparch".
Definition _swapHeap : ident := $"swapHeap".
Definition _tail : ident := $"tail".
Definition _tailItem : ident := $"tailItem".
Definition _temp : ident := $"temp".
Definition _treeItems : ident := $"treeItems".
Definition _value : ident := $"value".
Definition _values : ident := $"values".
Definition _width : ident := $"width".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

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
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _node (tptr (Tstruct __LLNode noattr)))
         (Tstruct __LLNode noattr)) _item (tptr (Tstruct __COOItem noattr))) ::
     nil))
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

Definition f_COOChunk_freeAll := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_chunk, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_head, (tptr (Tstruct __LLNode noattr))) ::
               (_next, (tptr (Tstruct __LLNode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _head
    (Efield
      (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
        (Tstruct __COOChunk noattr)) _head (tptr (Tstruct __LLNode noattr))))
  (Swhile
    (Etempvar _head (tptr (Tstruct __LLNode noattr)))
    (Ssequence
      (Sset _next
        (Efield
          (Ederef (Etempvar _head (tptr (Tstruct __LLNode noattr)))
            (Tstruct __LLNode noattr)) _next
          (tptr (Tstruct __LLNode noattr))))
      (Ssequence
        (Scall None
          (Evar _LLNode_freeAll (Tfunction
                                  (Tcons (tptr (Tstruct __LLNode noattr))
                                    Tnil) tvoid cc_default))
          ((Etempvar _head (tptr (Tstruct __LLNode noattr))) :: nil))
        (Sset _head (Etempvar _next (tptr (Tstruct __LLNode noattr))))))))
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
  (Ssequence
    (Sifthenelse (Efield
                   (Ederef
                     (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
                     (Tstruct __COOChunk noattr)) _tail
                   (tptr (Tstruct __LLNode noattr)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef
              (Efield
                (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
                  (Tstruct __COOChunk noattr)) _tail
                (tptr (Tstruct __LLNode noattr))) (Tstruct __LLNode noattr))
            _next (tptr (Tstruct __LLNode noattr)))
          (Etempvar _node (tptr (Tstruct __LLNode noattr))))
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
          (Etempvar _node (tptr (Tstruct __LLNode noattr))))))
    (Sassign
      (Efield
        (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
          (Tstruct __COOChunk noattr)) _len tuint)
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _chunk (tptr (Tstruct __COOChunk noattr)))
            (Tstruct __COOChunk noattr)) _len tuint)
        (Econst_int (Int.repr 1) tint) tuint))))
|}.

Definition f_COOChunk_append := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_left, (tptr (Tstruct __COOChunk noattr))) ::
                (_right, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Efield
               (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                 (Tstruct __COOChunk noattr)) _tail
               (tptr (Tstruct __LLNode noattr)))
  (Sifthenelse (Efield
                 (Ederef (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
                   (Tstruct __COOChunk noattr)) _tail
                 (tptr (Tstruct __LLNode noattr)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
            (Tstruct __COOChunk noattr)) _len tuint)
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _len tuint)
          (Efield
            (Ederef (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _len tuint) tuint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef
              (Efield
                (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
                  (Tstruct __COOChunk noattr)) _tail
                (tptr (Tstruct __LLNode noattr))) (Tstruct __LLNode noattr))
            _next (tptr (Tstruct __LLNode noattr)))
          (Efield
            (Ederef (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _head
            (tptr (Tstruct __LLNode noattr))))
        (Sassign
          (Efield
            (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _tail
            (tptr (Tstruct __LLNode noattr)))
          (Efield
            (Ederef (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _tail
            (tptr (Tstruct __LLNode noattr))))))
    Sskip)
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
          (Tstruct __COOChunk noattr)) _len tuint)
      (Efield
        (Ederef (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
          (Tstruct __COOChunk noattr)) _len tuint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
            (Tstruct __COOChunk noattr)) _head
          (tptr (Tstruct __LLNode noattr)))
        (Efield
          (Ederef (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
            (Tstruct __COOChunk noattr)) _head
          (tptr (Tstruct __LLNode noattr))))
      (Sassign
        (Efield
          (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
            (Tstruct __COOChunk noattr)) _tail
          (tptr (Tstruct __LLNode noattr)))
        (Efield
          (Ederef (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
            (Tstruct __COOChunk noattr)) _tail
          (tptr (Tstruct __LLNode noattr)))))))
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
               (_t'1, (tptr (Tstruct __CSRMatrix noattr))) :: nil);
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
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                    (Tstruct __CSRMatrix noattr)) _rows (tptr tuint))
                (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
            (Econst_int (Int.repr 0) tint))
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
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                (Tstruct __CSRMatrix noattr)) _values
                              (tptr tfloat)) (Etempvar _i tuint)
                            (tptr tfloat)) tfloat)
                        (Efield
                          (Ederef
                            (Etempvar _item (tptr (Tstruct __COOItem noattr)))
                            (Tstruct __COOItem noattr)) _value tfloat))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                  (Tstruct __CSRMatrix noattr)) _cols
                                (tptr tuint)) (Etempvar _i tuint)
                              (tptr tuint)) tuint)
                          (Efield
                            (Ederef
                              (Etempvar _item (tptr (Tstruct __COOItem noattr)))
                              (Tstruct __COOItem noattr)) _col tuint))
                        (Ssequence
                          (Swhile
                            (Ebinop Olt (Etempvar _rowId tuint)
                              (Efield
                                (Ederef
                                  (Etempvar _item (tptr (Tstruct __COOItem noattr)))
                                  (Tstruct __COOItem noattr)) _row tuint)
                              tint)
                            (Ssequence
                              (Sset _rowId
                                (Ebinop Oadd (Etempvar _rowId tuint)
                                  (Econst_int (Int.repr 1) tint) tuint))
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                        (Tstruct __CSRMatrix noattr)) _rows
                                      (tptr tuint)) (Etempvar _rowId tuint)
                                    (tptr tuint)) tuint)
                                (Ebinop Oadd (Etempvar _i tuint)
                                  (Econst_int (Int.repr 1) tint) tuint))))
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
                (Ebinop Ole (Etempvar _rowId tuint) (Etempvar _height tuint)
                  tint)
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                            (Tstruct __CSRMatrix noattr)) _rows (tptr tuint))
                        (Etempvar _rowId tuint) (tptr tuint)) tuint)
                    (Ebinop Omul (Etempvar _height tuint)
                      (Etempvar _width tuint) tuint))
                  (Sset _rowId
                    (Ebinop Oadd (Etempvar _rowId tuint)
                      (Econst_int (Int.repr 1) tint) tuint))))
              (Sreturn (Some (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr))))))))))))
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
               (_leftVal, tuint) :: (_row, tuint) :: (_rowId, tuint) ::
               (_rightRowStart, tuint) :: (_rightRowEnd, tuint) ::
               (_i__1, tuint) :: (_rightVal, tfloat) :: (_col, tuint) ::
               (_newItem, (tptr (Tstruct __COOItem noattr))) ::
               (_t'1, (tptr (Tstruct __COOItem noattr))) :: nil);
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
                        (Ecast
                          (Efield
                            (Ederef
                              (Etempvar _item (tptr (Tstruct __COOItem noattr)))
                              (Tstruct __COOItem noattr)) _value tfloat)
                          tuint))
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
                            (Sset _rightRowStart
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _right (tptr (Tstruct __CSRMatrix noattr)))
                                      (Tstruct __CSRMatrix noattr)) _rows
                                    (tptr tuint)) (Etempvar _rowId tuint)
                                  (tptr tuint)) tuint))
                            (Ssequence
                              (Sset _rightRowEnd
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _right (tptr (Tstruct __CSRMatrix noattr)))
                                        (Tstruct __CSRMatrix noattr)) _rows
                                      (tptr tuint))
                                    (Ebinop Oadd (Etempvar _rowId tuint)
                                      (Econst_int (Int.repr 1) tint) tuint)
                                    (tptr tuint)) tuint))
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
                                        (Sset _rightVal
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _right (tptr (Tstruct __CSRMatrix noattr)))
                                                  (Tstruct __CSRMatrix noattr))
                                                _values (tptr tfloat))
                                              (Etempvar _i__1 tuint)
                                              (tptr tfloat)) tfloat))
                                        (Ssequence
                                          (Sset _col
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _right (tptr (Tstruct __CSRMatrix noattr)))
                                                    (Tstruct __CSRMatrix noattr))
                                                  _cols (tptr tuint))
                                                (Etempvar _i__1 tuint)
                                                (tptr tuint)) tuint))
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
                                                   (Etempvar _leftVal tuint)
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

Definition f_mergeLow := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_left, (tptr (Tstruct __COOChunk noattr))) ::
                (_right, (tptr (Tstruct __COOChunk noattr))) ::
                (_result, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
Sskip
|}.

Definition f_mergeTop := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_left, (tptr (Tstruct __COOChunk noattr))) ::
                (_right, (tptr (Tstruct __COOChunk noattr))) ::
                (_result, (tptr (Tstruct __COOChunk noattr))) ::
                (_maxBound, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
Sskip
|}.

Definition f_elimZero := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_chunk, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn None)
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
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _li
    (Efield
      (Ederef (Etempvar _left (tptr (Tstruct __COOChunk noattr)))
        (Tstruct __COOChunk noattr)) _head (tptr (Tstruct __LLNode noattr))))
  (Ssequence
    (Sset _ri
      (Efield
        (Ederef (Etempvar _right (tptr (Tstruct __COOChunk noattr)))
          (Tstruct __COOChunk noattr)) _head
        (tptr (Tstruct __LLNode noattr))))
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
          (Sloop
            (Ssequence
              (Ssequence
                (Sifthenelse (Ebinop Oeq
                               (Etempvar _li (tptr (Tstruct __LLNode noattr)))
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) tint)
                  (Sset _t'1
                    (Ecast
                      (Ebinop Oeq
                        (Etempvar _ri (tptr (Tstruct __LLNode noattr)))
                        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                        tint) tbool))
                  (Sset _t'1 (Econst_int (Int.repr 0) tint)))
                (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
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
                          (Sifthenelse (Ebinop Olt
                                         (Efield
                                           (Ederef
                                             (Etempvar _litem (tptr (Tstruct __COOItem noattr)))
                                             (Tstruct __COOItem noattr)) _row
                                           tuint)
                                         (Efield
                                           (Ederef
                                             (Etempvar _ritem (tptr (Tstruct __COOItem noattr)))
                                             (Tstruct __COOItem noattr)) _row
                                           tuint) tint)
                            (Sset _t'2 (Econst_int (Int.repr 1) tint))
                            (Sifthenelse (Ebinop Oeq
                                           (Efield
                                             (Ederef
                                               (Etempvar _litem (tptr (Tstruct __COOItem noattr)))
                                               (Tstruct __COOItem noattr))
                                             _row tuint)
                                           (Efield
                                             (Ederef
                                               (Etempvar _ritem (tptr (Tstruct __COOItem noattr)))
                                               (Tstruct __COOItem noattr))
                                             _row tuint) tint)
                              (Ssequence
                                (Sset _t'2
                                  (Ecast
                                    (Ebinop Olt
                                      (Efield
                                        (Ederef
                                          (Etempvar _litem (tptr (Tstruct __COOItem noattr)))
                                          (Tstruct __COOItem noattr)) _row
                                        tuint)
                                      (Efield
                                        (Ederef
                                          (Etempvar _ritem (tptr (Tstruct __COOItem noattr)))
                                          (Tstruct __COOItem noattr)) _row
                                        tuint) tint) tbool))
                                (Sset _t'2
                                  (Ecast (Etempvar _t'2 tint) tbool)))
                              (Sset _t'2
                                (Ecast (Econst_int (Int.repr 0) tint) tbool))))
                          (Sifthenelse (Etempvar _t'2 tint)
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
                    (Sifthenelse (Efield
                                   (Ederef
                                     (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                                     (Tstruct __COOChunk noattr)) _tail
                                   (tptr (Tstruct __LLNode noattr)))
                      (Ssequence
                        (Sset _tailItem
                          (Efield
                            (Ederef
                              (Efield
                                (Ederef
                                  (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                                  (Tstruct __COOChunk noattr)) _tail
                                (tptr (Tstruct __LLNode noattr)))
                              (Tstruct __LLNode noattr)) _item
                            (tptr (Tstruct __COOItem noattr))))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                                (Tstruct __COOChunk noattr)) _len tuint)
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                                  (Tstruct __COOChunk noattr)) _len tuint)
                              (Econst_int (Int.repr 1) tint) tuint))
                          (Ssequence
                            (Sifthenelse (Ebinop Oeq
                                           (Efield
                                             (Ederef
                                               (Etempvar _item (tptr (Tstruct __COOItem noattr)))
                                               (Tstruct __COOItem noattr))
                                             _row tuint)
                                           (Efield
                                             (Ederef
                                               (Etempvar _tailItem (tptr (Tstruct __COOItem noattr)))
                                               (Tstruct __COOItem noattr))
                                             _row tuint) tint)
                              (Sset _t'3
                                (Ecast
                                  (Ebinop Oeq
                                    (Efield
                                      (Ederef
                                        (Etempvar _item (tptr (Tstruct __COOItem noattr)))
                                        (Tstruct __COOItem noattr)) _col
                                      tuint)
                                    (Efield
                                      (Ederef
                                        (Etempvar _tailItem (tptr (Tstruct __COOItem noattr)))
                                        (Tstruct __COOItem noattr)) _col
                                      tuint) tint) tbool))
                              (Sset _t'3 (Econst_int (Int.repr 0) tint)))
                            (Sifthenelse (Etempvar _t'3 tint)
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _tailItem (tptr (Tstruct __COOItem noattr)))
                                      (Tstruct __COOItem noattr)) _value
                                    tfloat)
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _tailItem (tptr (Tstruct __COOItem noattr)))
                                        (Tstruct __COOItem noattr)) _value
                                      tfloat)
                                    (Efield
                                      (Ederef
                                        (Etempvar _item (tptr (Tstruct __COOItem noattr)))
                                        (Tstruct __COOItem noattr)) _value
                                      tfloat) tfloat))
                                (Scall None
                                  (Evar _LLNode_freeAll (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct __LLNode noattr))
                                                            Tnil) tvoid
                                                          cc_default))
                                  ((Etempvar _node (tptr (Tstruct __LLNode noattr))) ::
                                   nil)))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Efield
                                      (Ederef
                                        (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                                        (Tstruct __COOChunk noattr)) _tail
                                      (tptr (Tstruct __LLNode noattr)))
                                    (Tstruct __LLNode noattr)) _next
                                  (tptr (Tstruct __LLNode noattr)))
                                (Etempvar _node (tptr (Tstruct __LLNode noattr))))))))
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
                            (Etempvar _node (tptr (Tstruct __LLNode noattr)))))))))))
            Sskip))))))
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
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
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
        (Sassign
          (Efield
            (Ederef (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _len tuint)
          (Efield
            (Ederef
              (Ederef
                (Ebinop Oadd
                  (Etempvar _chunks (tptr (tptr (Tstruct __COOChunk noattr))))
                  (Econst_int (Int.repr 0) tint)
                  (tptr (tptr (Tstruct __COOChunk noattr))))
                (tptr (Tstruct __COOChunk noattr)))
              (Tstruct __COOChunk noattr)) _len tuint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                (Tstruct __COOChunk noattr)) _head
              (tptr (Tstruct __LLNode noattr)))
            (Efield
              (Ederef
                (Ederef
                  (Ebinop Oadd
                    (Etempvar _chunks (tptr (tptr (Tstruct __COOChunk noattr))))
                    (Econst_int (Int.repr 0) tint)
                    (tptr (tptr (Tstruct __COOChunk noattr))))
                  (tptr (Tstruct __COOChunk noattr)))
                (Tstruct __COOChunk noattr)) _head
              (tptr (Tstruct __LLNode noattr))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                  (Tstruct __COOChunk noattr)) _tail
                (tptr (Tstruct __LLNode noattr)))
              (Efield
                (Ederef
                  (Ederef
                    (Ebinop Oadd
                      (Etempvar _chunks (tptr (tptr (Tstruct __COOChunk noattr))))
                      (Econst_int (Int.repr 0) tint)
                      (tptr (tptr (Tstruct __COOChunk noattr))))
                    (tptr (Tstruct __COOChunk noattr)))
                  (Tstruct __COOChunk noattr)) _tail
                (tptr (Tstruct __LLNode noattr))))
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
                  (Sassign
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Etempvar _merger (tptr (Tstruct __COOChunk noattr)))
                          (Etempvar _i tuint)
                          (tptr (Tstruct __COOChunk noattr)))
                        (Tstruct __COOChunk noattr)) _len tuint)
                    (Efield
                      (Ederef
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _chunks (tptr (tptr (Tstruct __COOChunk noattr))))
                            (Etempvar _i tuint)
                            (tptr (tptr (Tstruct __COOChunk noattr))))
                          (tptr (Tstruct __COOChunk noattr)))
                        (Tstruct __COOChunk noattr)) _len tuint))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _merger (tptr (Tstruct __COOChunk noattr)))
                            (Etempvar _i tuint)
                            (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _head
                        (tptr (Tstruct __LLNode noattr)))
                      (Efield
                        (Ederef
                          (Ederef
                            (Ebinop Oadd
                              (Etempvar _chunks (tptr (tptr (Tstruct __COOChunk noattr))))
                              (Etempvar _i tuint)
                              (tptr (tptr (Tstruct __COOChunk noattr))))
                            (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _head
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
                      (Efield
                        (Ederef
                          (Ederef
                            (Ebinop Oadd
                              (Etempvar _chunks (tptr (tptr (Tstruct __COOChunk noattr))))
                              (Etempvar _i tuint)
                              (tptr (tptr (Tstruct __COOChunk noattr))))
                            (tptr (Tstruct __COOChunk noattr)))
                          (Tstruct __COOChunk noattr)) _tail
                        (tptr (Tstruct __LLNode noattr)))))))
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
                              (Evar _merge (Tfunction
                                             (Tcons
                                               (tptr (Tstruct __COOChunk noattr))
                                               (Tcons
                                                 (tptr (Tstruct __COOChunk noattr))
                                                 (Tcons
                                                   (tptr (Tstruct __COOChunk noattr))
                                                   Tnil))) tvoid cc_default))
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
                            (Sassign
                              (Efield
                                (Ederef
                                  (Ebinop Oadd
                                    (Etempvar _merger (tptr (Tstruct __COOChunk noattr)))
                                    (Etempvar _i__2 tuint)
                                    (tptr (Tstruct __COOChunk noattr)))
                                  (Tstruct __COOChunk noattr)) _len tuint)
                              (Efield
                                (Ederef
                                  (Ebinop Oadd
                                    (Etempvar _temp (tptr (Tstruct __COOChunk noattr)))
                                    (Etempvar _i__2 tuint)
                                    (tptr (Tstruct __COOChunk noattr)))
                                  (Tstruct __COOChunk noattr)) _len tuint))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _merger (tptr (Tstruct __COOChunk noattr)))
                                      (Etempvar _i__2 tuint)
                                      (tptr (Tstruct __COOChunk noattr)))
                                    (Tstruct __COOChunk noattr)) _head
                                  (tptr (Tstruct __LLNode noattr)))
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
                                    (Tstruct __COOChunk noattr)) _tail
                                  (tptr (Tstruct __LLNode noattr)))
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _temp (tptr (Tstruct __COOChunk noattr)))
                                      (Etempvar _i__2 tuint)
                                      (tptr (Tstruct __COOChunk noattr)))
                                    (Tstruct __COOChunk noattr)) _tail
                                  (tptr (Tstruct __LLNode noattr)))))))
                        (Sset _i__2
                          (Ebinop Oadd (Etempvar _i__2 tuint)
                            (Econst_int (Int.repr 1) tint) tuint))))
                    (Sset _currLen (Etempvar _nextLen tuint))))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                    (Tstruct __COOChunk noattr)) _len tuint)
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Etempvar _merger (tptr (Tstruct __COOChunk noattr)))
                      (Econst_int (Int.repr 0) tint)
                      (tptr (Tstruct __COOChunk noattr)))
                    (Tstruct __COOChunk noattr)) _len tuint))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                      (Tstruct __COOChunk noattr)) _head
                    (tptr (Tstruct __LLNode noattr)))
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Etempvar _merger (tptr (Tstruct __COOChunk noattr)))
                        (Econst_int (Int.repr 0) tint)
                        (tptr (Tstruct __COOChunk noattr)))
                      (Tstruct __COOChunk noattr)) _head
                    (tptr (Tstruct __LLNode noattr))))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _result (tptr (Tstruct __COOChunk noattr)))
                        (Tstruct __COOChunk noattr)) _tail
                      (tptr (Tstruct __LLNode noattr)))
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Etempvar _merger (tptr (Tstruct __COOChunk noattr)))
                          (Econst_int (Int.repr 0) tint)
                          (tptr (Tstruct __COOChunk noattr)))
                        (Tstruct __COOChunk noattr)) _tail
                      (tptr (Tstruct __LLNode noattr))))
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
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _len (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                         (Efield
                           (Ederef
                             (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                             (Tstruct __CSRMatrix noattr)) _height tuint)
                         tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _rowCnt
              (Ebinop Osub
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                        (Tstruct __CSRMatrix noattr)) _rows (tptr tuint))
                    (Ebinop Oadd (Etempvar _i tuint)
                      (Econst_int (Int.repr 1) tint) tuint) (tptr tuint))
                  tuint)
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                        (Tstruct __CSRMatrix noattr)) _rows (tptr tuint))
                    (Etempvar _i tuint) (tptr tuint)) tuint) tuint))
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
                              (Sset _rowCnt__1
                                (Ebinop Osub
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                          (Tstruct __CSRMatrix noattr)) _rows
                                        (tptr tuint))
                                      (Ebinop Oadd (Etempvar _j tuint)
                                        (Econst_int (Int.repr 1) tint) tuint)
                                      (tptr tuint)) tuint)
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                          (Tstruct __CSRMatrix noattr)) _rows
                                        (tptr tuint)) (Etempvar _j tuint)
                                      (tptr tuint)) tuint) tuint))
                              (Sifthenelse (Ebinop Olt (Etempvar _i__1 tuint)
                                             (Etempvar _rowCnt__1 tuint)
                                             tint)
                                (Ssequence
                                  (Sset _idx
                                    (Ebinop Oadd
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Ederef
                                              (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                              (Tstruct __CSRMatrix noattr))
                                            _rows (tptr tuint))
                                          (Etempvar _j tuint) (tptr tuint))
                                        tuint) (Etempvar _i__1 tuint) tuint))
                                  (Ssequence
                                    (Sset _col
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Ederef
                                              (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                              (Tstruct __CSRMatrix noattr))
                                            _cols (tptr tuint))
                                          (Etempvar _idx tuint) (tptr tuint))
                                        tuint))
                                    (Ssequence
                                      (Sset _value
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                                (Tstruct __CSRMatrix noattr))
                                              _values (tptr tfloat))
                                            (Etempvar _idx tuint)
                                            (tptr tfloat)) tfloat))
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
  fn_temps := ((_temp, (tptr (Tstruct __COOChunk noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _temp
    (Ederef
      (Ebinop Oadd (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
        (Etempvar _i tuint) (tptr (tptr (Tstruct __COOChunk noattr))))
      (tptr (Tstruct __COOChunk noattr))))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
          (Etempvar _i tuint) (tptr (tptr (Tstruct __COOChunk noattr))))
        (tptr (Tstruct __COOChunk noattr)))
      (Ederef
        (Ebinop Oadd
          (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
          (Etempvar _j tuint) (tptr (tptr (Tstruct __COOChunk noattr))))
        (tptr (Tstruct __COOChunk noattr))))
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
               (_idx, tuint) :: (_parent, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oge
                 (Efield
                   (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
                     (Tstruct __PriorQ noattr)) _count tuint)
                 (Efield
                   (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
                     (Tstruct __PriorQ noattr)) _maxCount tuint) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Sset _heap
      (Efield
        (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
          (Tstruct __PriorQ noattr)) _heap
        (tptr (tptr (Tstruct __COOChunk noattr)))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
            (Tstruct __PriorQ noattr)) _count tuint)
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
              (Tstruct __PriorQ noattr)) _count tuint)
          (Econst_int (Int.repr 1) tint) tuint))
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
                (Sifthenelse (Ebinop Olt
                               (Efield
                                 (Ederef
                                   (Ederef
                                     (Ebinop Oadd
                                       (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                       (Etempvar _idx tuint)
                                       (tptr (tptr (Tstruct __COOChunk noattr))))
                                     (tptr (Tstruct __COOChunk noattr)))
                                   (Tstruct __COOChunk noattr)) _len tuint)
                               (Efield
                                 (Ederef
                                   (Ederef
                                     (Ebinop Oadd
                                       (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                       (Etempvar _parent tuint)
                                       (tptr (tptr (Tstruct __COOChunk noattr))))
                                     (tptr (Tstruct __COOChunk noattr)))
                                   (Tstruct __COOChunk noattr)) _len tuint)
                               tint)
                  (Scall None
                    (Evar _swapHeap (Tfunction
                                      (Tcons
                                        (tptr (tptr (Tstruct __COOChunk noattr)))
                                        (Tcons tuint (Tcons tuint Tnil)))
                                      tvoid cc_default))
                    ((Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr)))) ::
                     (Etempvar _idx tuint) :: (Etempvar _parent tuint) ::
                     nil))
                  Sskip)
                (Sset _idx (Etempvar _parent tuint))))))))))
|}.

Definition f_popQueue := {|
  fn_return := (tptr (Tstruct __COOChunk noattr));
  fn_callconv := cc_default;
  fn_params := ((_queue, (tptr (Tstruct __PriorQ noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_idx, tuint) :: (_count, tuint) ::
               (_heap, (tptr (tptr (Tstruct __COOChunk noattr)))) ::
               (_result, (tptr (Tstruct __COOChunk noattr))) ::
               (_leftIdx, tuint) :: (_rightIdx, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Efield
                   (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
                     (Tstruct __PriorQ noattr)) _count tuint)
                 (Econst_int (Int.repr 0) tint) tint)
    (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
    Sskip)
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
          (Tstruct __PriorQ noattr)) _count tuint)
      (Ebinop Osub
        (Efield
          (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
            (Tstruct __PriorQ noattr)) _count tuint)
        (Econst_int (Int.repr 1) tint) tuint))
    (Ssequence
      (Sset _idx (Econst_int (Int.repr 1) tint))
      (Ssequence
        (Sset _count
          (Efield
            (Ederef (Etempvar _queue (tptr (Tstruct __PriorQ noattr)))
              (Tstruct __PriorQ noattr)) _count tuint))
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
              (Scall None
                (Evar _swapHeap (Tfunction
                                  (Tcons
                                    (tptr (tptr (Tstruct __COOChunk noattr)))
                                    (Tcons tuint (Tcons tuint Tnil))) tvoid
                                  cc_default))
                ((Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr)))) ::
                 (Econst_int (Int.repr 0) tint) :: (Etempvar _count tuint) ::
                 nil))
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
                        (Sset _idx (Etempvar _leftIdx tuint))
                        (Sifthenelse (Ebinop Oeq (Etempvar _count tuint)
                                       (Etempvar _leftIdx tuint) tint)
                          (Ssequence
                            (Sifthenelse (Ebinop Ogt
                                           (Efield
                                             (Ederef
                                               (Ederef
                                                 (Ebinop Oadd
                                                   (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                                   (Etempvar _idx tuint)
                                                   (tptr (tptr (Tstruct __COOChunk noattr))))
                                                 (tptr (Tstruct __COOChunk noattr)))
                                               (Tstruct __COOChunk noattr))
                                             _len tuint)
                                           (Efield
                                             (Ederef
                                               (Ederef
                                                 (Ebinop Oadd
                                                   (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                                   (Etempvar _leftIdx tuint)
                                                   (tptr (tptr (Tstruct __COOChunk noattr))))
                                                 (tptr (Tstruct __COOChunk noattr)))
                                               (Tstruct __COOChunk noattr))
                                             _len tuint) tint)
                              (Scall None
                                (Evar _swapHeap (Tfunction
                                                  (Tcons
                                                    (tptr (tptr (Tstruct __COOChunk noattr)))
                                                    (Tcons tuint
                                                      (Tcons tuint Tnil)))
                                                  tvoid cc_default))
                                ((Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr)))) ::
                                 (Etempvar _idx tuint) ::
                                 (Etempvar _leftIdx tuint) :: nil))
                              Sskip)
                            (Sset _idx (Etempvar _leftIdx tuint)))
                          (Sifthenelse (Ebinop Ogt
                                         (Efield
                                           (Ederef
                                             (Ederef
                                               (Ebinop Oadd
                                                 (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                                 (Etempvar _idx tuint)
                                                 (tptr (tptr (Tstruct __COOChunk noattr))))
                                               (tptr (Tstruct __COOChunk noattr)))
                                             (Tstruct __COOChunk noattr))
                                           _len tuint)
                                         (Efield
                                           (Ederef
                                             (Ederef
                                               (Ebinop Oadd
                                                 (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                                 (Etempvar _leftIdx tuint)
                                                 (tptr (tptr (Tstruct __COOChunk noattr))))
                                               (tptr (Tstruct __COOChunk noattr)))
                                             (Tstruct __COOChunk noattr))
                                           _len tuint) tint)
                            (Sifthenelse (Ebinop Ogt
                                           (Efield
                                             (Ederef
                                               (Ederef
                                                 (Ebinop Oadd
                                                   (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                                   (Etempvar _idx tuint)
                                                   (tptr (tptr (Tstruct __COOChunk noattr))))
                                                 (tptr (Tstruct __COOChunk noattr)))
                                               (Tstruct __COOChunk noattr))
                                             _len tuint)
                                           (Efield
                                             (Ederef
                                               (Ederef
                                                 (Ebinop Oadd
                                                   (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                                   (Etempvar _rightIdx tuint)
                                                   (tptr (tptr (Tstruct __COOChunk noattr))))
                                                 (tptr (Tstruct __COOChunk noattr)))
                                               (Tstruct __COOChunk noattr))
                                             _len tuint) tint)
                              (Sifthenelse (Ebinop Olt
                                             (Efield
                                               (Ederef
                                                 (Ederef
                                                   (Ebinop Oadd
                                                     (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                                     (Etempvar _leftIdx tuint)
                                                     (tptr (tptr (Tstruct __COOChunk noattr))))
                                                   (tptr (Tstruct __COOChunk noattr)))
                                                 (Tstruct __COOChunk noattr))
                                               _len tuint)
                                             (Efield
                                               (Ederef
                                                 (Ederef
                                                   (Ebinop Oadd
                                                     (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                                     (Etempvar _rightIdx tuint)
                                                     (tptr (tptr (Tstruct __COOChunk noattr))))
                                                   (tptr (Tstruct __COOChunk noattr)))
                                                 (Tstruct __COOChunk noattr))
                                               _len tuint) tint)
                                (Ssequence
                                  (Scall None
                                    (Evar _swapHeap (Tfunction
                                                      (Tcons
                                                        (tptr (tptr (Tstruct __COOChunk noattr)))
                                                        (Tcons tuint
                                                          (Tcons tuint Tnil)))
                                                      tvoid cc_default))
                                    ((Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr)))) ::
                                     (Etempvar _idx tuint) ::
                                     (Etempvar _leftIdx tuint) :: nil))
                                  (Sset _idx (Etempvar _leftIdx tuint)))
                                (Ssequence
                                  (Scall None
                                    (Evar _swapHeap (Tfunction
                                                      (Tcons
                                                        (tptr (tptr (Tstruct __COOChunk noattr)))
                                                        (Tcons tuint
                                                          (Tcons tuint Tnil)))
                                                      tvoid cc_default))
                                    ((Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr)))) ::
                                     (Etempvar _idx tuint) ::
                                     (Etempvar _rightIdx tuint) :: nil))
                                  (Sset _idx (Etempvar _rightIdx tuint))))
                              (Ssequence
                                (Scall None
                                  (Evar _swapHeap (Tfunction
                                                    (Tcons
                                                      (tptr (tptr (Tstruct __COOChunk noattr)))
                                                      (Tcons tuint
                                                        (Tcons tuint Tnil)))
                                                    tvoid cc_default))
                                  ((Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr)))) ::
                                   (Etempvar _idx tuint) ::
                                   (Etempvar _leftIdx tuint) :: nil))
                                (Sset _idx (Etempvar _leftIdx tuint))))
                            (Sifthenelse (Ebinop Ogt
                                           (Efield
                                             (Ederef
                                               (Ederef
                                                 (Ebinop Oadd
                                                   (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                                   (Etempvar _idx tuint)
                                                   (tptr (tptr (Tstruct __COOChunk noattr))))
                                                 (tptr (Tstruct __COOChunk noattr)))
                                               (Tstruct __COOChunk noattr))
                                             _len tuint)
                                           (Efield
                                             (Ederef
                                               (Ederef
                                                 (Ebinop Oadd
                                                   (Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr))))
                                                   (Etempvar _rightIdx tuint)
                                                   (tptr (tptr (Tstruct __COOChunk noattr))))
                                                 (tptr (Tstruct __COOChunk noattr)))
                                               (Tstruct __COOChunk noattr))
                                             _len tuint) tint)
                              (Ssequence
                                (Scall None
                                  (Evar _swapHeap (Tfunction
                                                    (Tcons
                                                      (tptr (tptr (Tstruct __COOChunk noattr)))
                                                      (Tcons tuint
                                                        (Tcons tuint Tnil)))
                                                    tvoid cc_default))
                                  ((Etempvar _heap (tptr (tptr (Tstruct __COOChunk noattr)))) ::
                                   (Etempvar _idx tuint) ::
                                   (Etempvar _rightIdx tuint) :: nil))
                                (Sset _idx (Etempvar _rightIdx tuint)))
                              (Sset _idx (Etempvar _rightIdx tuint)))))))))
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
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _matrix (tptr (Tstruct __Matrix noattr)))
         (Tstruct __Matrix noattr)) _values (tptr tfloat)) :: nil))
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
               (_t'1, (tptr (Tstruct __CSRMatrix noattr))) :: nil);
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
                (Sifthenelse (Ebinop One
                               (Ederef
                                 (Ebinop Oadd
                                   (Efield
                                     (Ederef
                                       (Etempvar _matrix (tptr (Tstruct __Matrix noattr)))
                                       (Tstruct __Matrix noattr)) _values
                                     (tptr tfloat)) (Etempvar _i tuint)
                                   (tptr tfloat)) tfloat)
                               (Econst_float (Float.of_bits (Int64.repr 0)) tdouble)
                               tint)
                  (Sset _lenVal
                    (Ebinop Oadd (Etempvar _lenVal tuint)
                      (Econst_int (Int.repr 1) tint) tuint))
                  Sskip))
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
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                          (Tstruct __CSRMatrix noattr)) _rows (tptr tuint))
                      (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
                  (Econst_int (Int.repr 0) tint))
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
                                    (Sset _value
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Ederef
                                              (Etempvar _matrix (tptr (Tstruct __Matrix noattr)))
                                              (Tstruct __Matrix noattr))
                                            _values (tptr tfloat))
                                          (Etempvar _offset tuint)
                                          (tptr tfloat)) tfloat))
                                    (Sifthenelse (Ebinop One
                                                   (Etempvar _value tfloat)
                                                   (Econst_float (Float.of_bits (Int64.repr 0)) tdouble)
                                                   tint)
                                      (Ssequence
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                                  (Tstruct __CSRMatrix noattr))
                                                _values (tptr tfloat))
                                              (Etempvar _index tuint)
                                              (tptr tfloat)) tfloat)
                                          (Etempvar _value tfloat))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                                    (Tstruct __CSRMatrix noattr))
                                                  _cols (tptr tuint))
                                                (Etempvar _index tuint)
                                                (tptr tuint)) tuint)
                                            (Etempvar _j tuint))
                                          (Sset _index
                                            (Ebinop Oadd
                                              (Etempvar _index tuint)
                                              (Econst_int (Int.repr 1) tint)
                                              tuint))))
                                      Sskip))))
                              (Sset _j
                                (Ebinop Oadd (Etempvar _j tuint)
                                  (Econst_int (Int.repr 1) tint) tuint))))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                    (Tstruct __CSRMatrix noattr)) _rows
                                  (tptr tuint))
                                (Ebinop Oadd (Etempvar _i__1 tuint)
                                  (Econst_int (Int.repr 1) tint) tuint)
                                (tptr tuint)) tuint) (Etempvar _index tuint))))
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
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
         (Tstruct __CSRMatrix noattr)) _values (tptr tfloat)) :: nil))
  (Ssequence
    (Scall None
      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Efield
         (Ederef (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
           (Tstruct __CSRMatrix noattr)) _cols (tptr tuint)) :: nil))
    (Ssequence
      (Scall None
        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Efield
           (Ederef (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
             (Tstruct __CSRMatrix noattr)) _rows (tptr tuint)) :: nil))
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
               (_t'1, (tptr (Tstruct __Matrix noattr))) :: nil);
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
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _mat (tptr (Tstruct __Matrix noattr)))
                          (Tstruct __Matrix noattr)) _values (tptr tfloat))
                      (Etempvar _i tuint) (tptr tfloat)) tfloat)
                  (Econst_int (Int.repr 0) tint)))
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
                    (Sset _rowStart
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                              (Tstruct __CSRMatrix noattr)) _rows
                            (tptr tuint)) (Etempvar _i__1 tuint)
                          (tptr tuint)) tuint))
                    (Ssequence
                      (Sset _rowEnd
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                (Tstruct __CSRMatrix noattr)) _rows
                              (tptr tuint))
                            (Ebinop Oadd (Etempvar _i__1 tuint)
                              (Econst_int (Int.repr 1) tint) tuint)
                            (tptr tuint)) tuint))
                      (Ssequence
                        (Sset _j (Etempvar _rowStart tuint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _j tuint)
                                           (Etempvar _rowEnd tuint) tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Sset _idx
                                (Ebinop Oadd
                                  (Ebinop Omul (Etempvar _i__1 tuint)
                                    (Etempvar _width tuint) tuint)
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                          (Tstruct __CSRMatrix noattr)) _cols
                                        (tptr tuint)) (Etempvar _j tuint)
                                      (tptr tuint)) tuint) tuint))
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _mat (tptr (Tstruct __Matrix noattr)))
                                        (Tstruct __Matrix noattr)) _values
                                      (tptr tfloat)) (Etempvar _idx tuint)
                                    (tptr tfloat)) tfloat)
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr)))
                                        (Tstruct __CSRMatrix noattr)) _values
                                      (tptr tfloat)) (Etempvar _j tuint)
                                    (tptr tfloat)) tfloat))))
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
               (_t'9, (tptr (Tstruct __CSRMatrix noattr))) ::
               (_t'8, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'7, (tptr (Tstruct __COOChunk noattr))) :: (_t'6, tuint) ::
               (_t'5, (tptr (Tstruct __COOChunk noattr))) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr (tptr (Tstruct __COOChunk noattr)))) :: nil);
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
        (Scall (Some _t'2)
          (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                          cc_default))
          ((Ebinop Omul (Evar _leftLen tuint)
             (Esizeof (Tstruct __COOChunk noattr) tuint) tuint) :: nil))
        (Sset _multVal
          (Ecast (Etempvar _t'2 (tptr tvoid))
            (tptr (Tstruct __COOChunk noattr)))))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                             (Evar _leftLen tuint) tint)
                Sskip
                Sbreak)
              (Scall None
                (Evar _outerProd (Tfunction
                                   (Tcons (tptr (Tstruct __COOChunk noattr))
                                     (Tcons
                                       (tptr (Tstruct __CSRMatrix noattr))
                                       (Tcons
                                         (tptr (Tstruct __COOChunk noattr))
                                         Tnil))) tvoid cc_default))
                ((Ederef
                   (Ebinop Oadd
                     (Etempvar _leftChunk (tptr (tptr (Tstruct __COOChunk noattr))))
                     (Etempvar _i tuint)
                     (tptr (tptr (Tstruct __COOChunk noattr))))
                   (tptr (Tstruct __COOChunk noattr))) ::
                 (Etempvar _matB (tptr (Tstruct __CSRMatrix noattr))) ::
                 (Ebinop Oadd
                   (Etempvar _multVal (tptr (Tstruct __COOChunk noattr)))
                   (Etempvar _i tuint) (tptr (Tstruct __COOChunk noattr))) ::
                 nil)))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
                tuint))))
        (Ssequence
          (Sassign (Efield (Evar _pq (Tstruct __PriorQ noattr)) _count tuint)
            (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Efield (Evar _pq (Tstruct __PriorQ noattr)) _maxCount tuint)
              (Evar _leftLen tuint))
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                  cc_default))
                  ((Ebinop Omul
                     (Ebinop Oadd (Evar _leftLen tuint)
                       (Econst_int (Int.repr 1) tint) tuint)
                     (Esizeof (tptr (Tstruct __COOChunk noattr)) tuint)
                     tuint) :: nil))
                (Sassign
                  (Efield (Evar _pq (Tstruct __PriorQ noattr)) _heap
                    (tptr (tptr (Tstruct __COOChunk noattr))))
                  (Ecast (Etempvar _t'3 (tptr tvoid))
                    (tptr (tptr (Tstruct __COOChunk noattr))))))
              (Ssequence
                (Ssequence
                  (Sset _i__1 (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _i__1 tuint)
                                     (Evar _leftLen tuint) tint)
                        Sskip
                        Sbreak)
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
                    (Sset _kInit
                      (Ebinop Oadd
                        (Ebinop Omod
                          (Ebinop Osub (Evar _leftLen tuint)
                            (Econst_int (Int.repr 2) tint) tuint)
                          (Ebinop Osub (Econst_int (Int.repr 64) tint)
                            (Econst_int (Int.repr 1) tint) tint) tuint)
                        (Econst_int (Int.repr 2) tint) tuint))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'4)
                          (Evar _malloc (Tfunction (Tcons tuint Tnil)
                                          (tptr tvoid) cc_default))
                          ((Ebinop Omul
                             (Ebinop Oadd
                               (Ebinop Odiv (Evar _leftLen tuint)
                                 (Ebinop Osub (Econst_int (Int.repr 64) tint)
                                   (Econst_int (Int.repr 1) tint) tint)
                                 tuint) (Econst_int (Int.repr 1) tint) tuint)
                             (Esizeof (Tstruct __COOChunk noattr) tuint)
                             tuint) :: nil))
                        (Sset _mergedVal
                          (Ecast (Etempvar _t'4 (tptr tvoid))
                            (tptr (Tstruct __COOChunk noattr)))))
                      (Ssequence
                        (Ssequence
                          (Sset _i__2 (Econst_int (Int.repr 0) tint))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Olt (Etempvar _i__2 tuint)
                                             (Etempvar _kInit tuint) tint)
                                Sskip
                                Sbreak)
                              (Ssequence
                                (Scall (Some _t'5)
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
                                  (Etempvar _t'5 (tptr (Tstruct __COOChunk noattr))))))
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
                                                    Tnil)) tvoid cc_default))
                              ((Eaddrof (Evar _pq (Tstruct __PriorQ noattr))
                                 (tptr (Tstruct __PriorQ noattr))) ::
                               (Ebinop Oadd
                                 (Etempvar _mergedVal (tptr (Tstruct __COOChunk noattr)))
                                 (Econst_int (Int.repr 0) tint)
                                 (tptr (Tstruct __COOChunk noattr))) :: nil))
                            (Ssequence
                              (Sset _mergedIdx
                                (Ebinop Oadd (Etempvar _mergedIdx tuint)
                                  (Econst_int (Int.repr 1) tint) tuint))
                              (Ssequence
                                (Swhile
                                  (Ebinop Ogt
                                    (Efield
                                      (Evar _pq (Tstruct __PriorQ noattr))
                                      _count tuint)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  (Ssequence
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Efield
                                                       (Evar _pq (Tstruct __PriorQ noattr))
                                                       _count tuint)
                                                     (Econst_int (Int.repr 64) tint)
                                                     tint)
                                        (Sset _t'6
                                          (Ecast
                                            (Efield
                                              (Evar _pq (Tstruct __PriorQ noattr))
                                              _count tuint) tuint))
                                        (Sset _t'6
                                          (Ecast
                                            (Econst_int (Int.repr 64) tint)
                                            tuint)))
                                      (Sset _count (Etempvar _t'6 tuint)))
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
                                                    (Etempvar _i__3 tuint)
                                                    (tptr (tptr (Tstruct __COOChunk noattr))))
                                                  (tptr (Tstruct __COOChunk noattr)))
                                                (Etempvar _t'7 (tptr (Tstruct __COOChunk noattr))))))
                                          (Sset _i__3
                                            (Ebinop Oadd
                                              (Etempvar _i__3 tuint)
                                              (Econst_int (Int.repr 1) tint)
                                              tuint))))
                                      (Ssequence
                                        (Scall None
                                          (Evar _flattenByMergeTree (Tfunction
                                                                    (Tcons
                                                                    (tptr (tptr (Tstruct __COOChunk noattr)))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    (tptr (Tstruct __COOChunk noattr))
                                                                    Tnil)))
                                                                    tvoid
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
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'8)
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
                                      (Etempvar _t'8 (tptr (Tstruct __COOChunk noattr)))))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'9)
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
                                         (Efield
                                           (Ederef
                                             (Etempvar _matA (tptr (Tstruct __CSRMatrix noattr)))
                                             (Tstruct __CSRMatrix noattr))
                                           _height tuint) ::
                                         (Efield
                                           (Ederef
                                             (Etempvar _matB (tptr (Tstruct __CSRMatrix noattr)))
                                             (Tstruct __CSRMatrix noattr))
                                           _width tuint) :: nil))
                                      (Sset _csr
                                        (Etempvar _t'9 (tptr (Tstruct __CSRMatrix noattr)))))
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
                                                (Sifthenelse (Ebinop Olt
                                                               (Etempvar _i__4 tuint)
                                                               (Evar _leftLen tuint)
                                                               tint)
                                                  Sskip
                                                  Sbreak)
                                                (Scall None
                                                  (Evar _COOChunk_free 
                                                  (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct __COOChunk noattr))
                                                      Tnil) tvoid cc_default))
                                                  ((Ederef
                                                     (Ebinop Oadd
                                                       (Etempvar _leftChunk (tptr (tptr (Tstruct __COOChunk noattr))))
                                                       (Etempvar _i__4 tuint)
                                                       (tptr (tptr (Tstruct __COOChunk noattr))))
                                                     (tptr (Tstruct __COOChunk noattr))) ::
                                                   nil)))
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
                                              (Scall None
                                                (Evar _free (Tfunction
                                                              (Tcons
                                                                (tptr tvoid)
                                                                Tnil) tvoid
                                                              cc_default))
                                                ((Efield
                                                   (Evar _pq (Tstruct __PriorQ noattr))
                                                   _heap
                                                   (tptr (tptr (Tstruct __COOChunk noattr)))) ::
                                                 nil))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _free (Tfunction
                                                                (Tcons
                                                                  (tptr tvoid)
                                                                  Tnil) tvoid
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
                                                  (Sreturn (Some (Etempvar _csr (tptr (Tstruct __CSRMatrix noattr))))))))))))))))))))))))))))))
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
((___builtin_ais_annot,
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
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_LLNode_malloc, Gfun(Internal f_LLNode_malloc)) ::
 (_LLNode_free, Gfun(Internal f_LLNode_free)) ::
 (_LLNode_freeAll, Gfun(Internal f_LLNode_freeAll)) ::
 (_COOChunk_malloc, Gfun(Internal f_COOChunk_malloc)) ::
 (_COOChunk_free, Gfun(Internal f_COOChunk_free)) ::
 (_COOChunk_freeAll, Gfun(Internal f_COOChunk_freeAll)) ::
 (_COOChunk_push, Gfun(Internal f_COOChunk_push)) ::
 (_COOChunk_append, Gfun(Internal f_COOChunk_append)) ::
 (_COOChunk_toCSR, Gfun(Internal f_COOChunk_toCSR)) ::
 (_outerProd, Gfun(Internal f_outerProd)) ::
 (_mergeLow, Gfun(Internal f_mergeLow)) ::
 (_mergeTop, Gfun(Internal f_mergeTop)) ::
 (_elimZero, Gfun(Internal f_elimZero)) ::
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
 (_gemm_sparch, Gfun(Internal f_gemm_sparch)) :: nil).

Definition public_idents : list ident :=
(_gemm_sparch :: _spgemm_sparch :: _CSR_dense :: _CSR_free :: _CSR_malloc ::
 _Matrix_toCSR :: _Matrix_free :: _Matrix_malloc :: _COOItem_free ::
 _COOItem_malloc :: _popQueue :: _addQueue :: _swapHeap :: _condense ::
 _flattenByMergeTree :: _merge :: _elimZero :: _mergeTop :: _mergeLow ::
 _outerProd :: _COOChunk_toCSR :: _COOChunk_append :: _COOChunk_push ::
 _COOChunk_freeAll :: _COOChunk_free :: _COOChunk_malloc ::
 _LLNode_freeAll :: _LLNode_free :: _LLNode_malloc :: _free :: _malloc ::
 ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


