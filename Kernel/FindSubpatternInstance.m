Package["Wolfram`Patterns`"]

PackageExport["FindSubpatternInstance"]
PackageExport["FindNegativeSubpatternInstance"]



(* FindSubpatternInstance *)

Options[FindSubpatternInstance] = {MaxItems -> 1}

FindSubpatternInstance[Verbatim[Blank][head_], OptionsPattern[]] := FindHeadInstance[head, OptionValue[MaxItems]]

FindSubpatternInstance[_Blank, OptionsPattern[]] := {_}

FindSubpatternInstance[_BlankSequence, OptionsPattern[]] := {Inactive[Sequence][_]}

FindSubpatternInstance[Verbatim[BlankSequence][head_], OptionsPattern[]] := Inactive[Sequence] /@ FindHeadInstance[head, OptionValue[MaxItems]]

FindSubpatternInstance[_BlankNullSequence, OptionsPattern[]] := {Inactive[Sequence][]}

FindSubpatternInstance[Verbatim[BlankNullSequence][_], OptionsPattern[]] := {Inactive[Sequence][]}

FindSubpatternInstance[Verbatim[Pattern][_, patt_] | Verbatim[HoldPattern][patt_], opts : OptionsPattern[]] :=
    FindSubpatternInstance[Unevaluated @ patt, opts]

FindSubpatternInstance[patt_Alternatives, opts : OptionsPattern[]] :=
    FoldWhile[Function[Null, Union[#1, FindSubpatternInstance[Unevaluated @ #2, opts]], HoldAllComplete], {}, Unevaluated @ patt, Length[#] < OptionValue[MaxItems] &]

FindSubpatternInstance[Except[patt_], opts : OptionsPattern[]] := FindNegativeSubpatternInstance[Unevaluated @ patt, opts]

FindSubpatternInstance[atom_ ? AtomQ, OptionsPattern[]] := {atom}


(* FindNegativeSubpatternInstance *)

Options[FindNegativeSubpatternInstance] = {MaxItems -> 1}

FindNegativeSubpatternInstance[Verbatim[Blank][head_], OptionsPattern[]] := FindHeadInstance[head, OptionValue[MaxItems]]

FindNegativeSubpatternInstance[_Blank, OptionsPattern[]] := {_}

FindNegativeSubpatternInstance[_BlankSequence, OptionsPattern[]] := {Inactive[Sequence][_]}

FindNegativeSubpatternInstance[Verbatim[BlankSequence][head_], OptionsPattern[]] := Inactive[Sequence] /@ FindHeadInstance[head, OptionValue[MaxItems]]

FindNegativeSubpatternInstance[_BlankNullSequence, OptionsPattern[]] := {Inactive[Sequence][]}

FindNegativeSubpatternInstance[Verbatim[BlankNullSequence][_], OptionsPattern[]] := {Inactive[Sequence][]}

FindNegativeSubpatternInstance[Verbatim[Pattern][_, patt_] | Verbatim[HoldPattern][patt_], opts : OptionsPattern[]] :=
    FindNegativeSubpatternInstance[Unevaluated @ patt, opts]

FindNegativeSubpatternInstance[patt_Alternatives, opts : OptionsPattern[]] :=
    FoldWhile[Function[Null, Union[#1, FindSubpatternInstance[Unevaluated @ #2, opts]], HoldAllComplete], {}, Unevaluated @ patt, Length[#] < OptionValue[MaxItems] &]

FindNegativeSubpatternInstance[Except[patt_], opts : OptionsPattern[]] := FindSubpatternInstance[Unevaluated @ patt, opts]

FindNegativeSubpatternInstance[_ ? AtomQ, OptionsPattern[]] := {False}

FindNegativeSubpatternInstance[False, OptionsPattern[]] := {True}



FindHeadInstance[Integer, n_Integer] := RandomInteger[{0, Max[100, n ^ 2]}, n]

FindHeadInstance[Real, n_Integer] := RandomReal[{0, Max[100, n ^ 2]}, n]

