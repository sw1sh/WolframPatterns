Package["Wolfram`Patterns`"]

PackageExport["PatternSubstitutions"]



tripleSplits[args_, l_, r_, defaultMode_ : Automatic] := With[{mode = Replace[defaultMode, Automatic -> If[l > 0, Longest, Shortest]]}, Which[
	l == 0 && r == 0,
	{{HoldComplete[], args, HoldComplete[]}},
	l == 0,
	Prepend[HoldComplete[]] /@ If[mode === Longest, Reverse, Identity] @ splits[args, 2],
	r == 0,
	Append[HoldComplete[]] /@ If[mode === Shortest, Reverse, Identity] @ splits[args, 2],
	True,
	Switch[mode, Shortest, SortBy[Length[#[[2]]] &], Longest, ReverseSortBy[Length[#[[2]]] &], _, Identity] @ splits[args, 3]
]
]


PatternSubstitutions[expr_, patt_] := PatternSubstitutions[Unevaluated[expr], Unevaluated[patt], Infinity]


PatternSubstitutions[head_Symbol[args___], head_Symbol[patt___], n_] /;
    Not[Length[Unevaluated[{patt}]] == 1 && Head[Unevaluated[patt]] === OrderlessPatternSequence] && MemberQ[Attributes[head], Orderless] :=
    Block[{h},
        SetAttributes[h, DeleteCases[Attributes[head], Orderless]];
        PatternSubstitutions[Unevaluated[h[args]], Unevaluated[h[OrderlessPatternSequence[patt]]], n] /. h :> head
    ]


(* Shortest *)

PatternSubstitutions[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[Shortest][patt_], right___], n_] := With[{shift = Length[HoldComplete[left]]},
	SubstitutionExpand[
		SubstitutionSum @@ Apply[SubstitutionMerge[
			With[{val = Unevaluated @@ head @@@ HoldComplete[#1]}, PatternSubstitutions[val, Unevaluated[head[left]]]],
			PartSubstitution[{shift + 1},
				HoldPattern[mid],
				With[{val = Unevaluated @@ head @@@ HoldComplete[#2]}, PatternSubstitutions[val, Unevaluated[head[patt]]]  /. PartSubstitution[part_, rest__] :> PartSubstitution[Rest[part], rest]]
			],
			With[{val = Unevaluated @@ head @@@ HoldComplete[#3]}, PatternSubstitutions[val, Unevaluated[head[right]]] /. PartSubstitution[part_, rest__] :> PartSubstitution[Prepend[Rest[part], shift + 2], rest]]
		] &] /@ tripleSplits[HoldComplete[args], Length[HoldComplete[left]], Length[HoldComplete[right]], Shortest],
		n
	]
]


(* Longest *)

PatternSubstitutions[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[Longest][patt_], right___], n_] := With[{shift = Length[HoldComplete[left]]},
	SubstitutionExpand[
		SubstitutionSum @@ Apply[SubstitutionMerge[
			With[{val = Unevaluated @@ head @@@ HoldComplete[#1]}, PatternSubstitutions[val, Unevaluated[head[left]]]],
			PartSubstitution[{shift + 1},
				HoldPattern[mid],
				With[{val = Unevaluated @@ head @@@ HoldComplete[#2]}, PatternSubstitutions[val, Unevaluated[head[patt]]]  /. PartSubstitution[part_, rest__] :> PartSubstitution[Rest[part], rest]]
			],
			With[{val = Unevaluated @@ head @@@ HoldComplete[#3]}, PatternSubstitutions[val, Unevaluated[head[right]]] /. PartSubstitution[part_, rest__] :> PartSubstitution[Prepend[Rest[part], shift + 2], rest]]
		] &] /@ tripleSplits[HoldComplete[args], Length[HoldComplete[left]], Length[HoldComplete[right]], Longest],
		n
	]
]


(* Pattern *)

PatternSubstitutions[expr_, patt : Verbatim[Pattern][_Symbol, subPatt_], n_] :=
	PartSubstitution[{}, HoldPattern[patt], PartSubstitution[{}, HoldPattern[subPatt], PatternSubstitutions[Unevaluated[expr], Unevaluated[subPatt], n]]]

PatternSubstitutions[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[Pattern][_Symbol, patt_], right___], n_] := With[{shift = Length[HoldComplete[left]]},
	SubstitutionExpand[
		SubstitutionSum @@ Apply[SubstitutionMerge[
            If[ Length[HoldComplete[left]] > 0,
			    With[{val = Unevaluated @@ head @@@ HoldComplete[#1]}, PatternSubstitutions[val, Unevaluated[head[left]]]],
                SubstitutionValues[]
            ],
			PartSubstitution[{shift + 1},
				HoldPattern[mid],
				With[{val = Unevaluated @@ head @@@ HoldComplete[#2]}, PatternSubstitutions[val, Unevaluated[head[patt]]] /.
                    PartSubstitution[part_, rest__] :> PartSubstitution[Rest[part], rest]]
			],
            If[ Length[HoldComplete[right]] > 0,
                With[{val = Unevaluated @@ head @@@ HoldComplete[#3]}, PatternSubstitutions[val, Unevaluated[head[right]]] /.
                    PartSubstitution[part_, rest__] :> PartSubstitution[Prepend[Rest[part], shift + 2], rest]],
                SubstitutionValues[]
            ]
		] &] /@ tripleSplits[HoldComplete[args], Length[HoldComplete[left]], Length[HoldComplete[right]]],
		n
	]
]


(* Blank *)

PatternSubstitutions[expr_, Verbatim[Blank][], _] := SubstitutionValues[expr]

PatternSubstitutions[expr_, Verbatim[Blank][h_], n_] := With[{head = Unevaluated @@ Head[Unevaluated[expr], HoldComplete]},
	SubstitutionMerge[PatternSubstitutions[head, h, n], SubstitutionValues[expr]]]


PatternSubstitutions[head_Symbol[args___], head_Symbol[left___, Verbatim[Blank][h___], right___], n_] :=
	FoldTakeWhile[
		With[{valLeft = Unevaluated @@ head @@@ HoldComplete @@ {#[[1]]}, valRight = Unevaluated @@ head @@@ HoldComplete @@ {#[[3]]}},
			SubstitutionExpand[
				SubstitutionMerge[
					If[ Length[HoldComplete[left]] > 0,
                        PartSubstitution[{1}, HoldPattern[head[left]], PatternSubstitutions[valLeft, Unevaluated[head[left]]]],
                        SubstitutionValues[]
                    ],
					PartSubstitution[{Length[HoldComplete[left]] + 1}, HoldPattern[Blank[h]],
                        HoldApply[
                            If[Length[#[[2]]] > 1 && (MemberQ[Attributes[head], Flat] || MemberQ[Attributes[head], OneIdentity]), head, Sequence],
                            #[[2]],
                            SubstitutionValues
                        ]
                    ],
					If[ Length[HoldComplete[right]] > 0,
                        PartSubstitution[{Length[HoldComplete[left]] + 2}, HoldPattern[head[right]], PatternSubstitutions[valRight, Unevaluated[head[right]]]],
                        SubstitutionValues[]
                    ]
				],
				n
			]
		] &,
        If[MemberQ[Attributes[head], Flat], Identity, Select[MatchQ[#[[2]], HoldComplete[_h]] &]] @
            tripleSplits[HoldComplete[args], Length[HoldComplete[left]], Length[HoldComplete[right]]],
		n,
        SubstitutionSum
	]


(* BlankSequence *)

PatternSubstitutions[head_Symbol[args__], head_Symbol[left___, Verbatim[BlankSequence][h___], right___], n_] :=
	FoldTakeWhile[
		With[{valLeft = Unevaluated @@ head @@@ HoldComplete @@ {#[[1]]}, valRight = Unevaluated @@ head @@@ HoldComplete @@ {#[[3]]}},
			SubstitutionExpand[
				SubstitutionMerge[
                    If[ Length[HoldComplete[left]] > 0,
					    PartSubstitution[{1}, HoldPattern[head[left]], PatternSubstitutions[valLeft, Unevaluated[head[left]]]],
                        SubstitutionValues[]
                    ],
					PartSubstitution[{Length[HoldComplete[left]] + 1}, HoldPattern[BlankSequence[h]], HoldApply[Sequence, #[[2]], SubstitutionValues]],
                    If[ Length[HoldComplete[right]] > 0,
					    PartSubstitution[{Length[HoldComplete[left]] + 2}, HoldPattern[head[right]], PatternSubstitutions[valRight, Unevaluated[head[right]]]],
                        SubstitutionValues[]
                    ]
				],
				n
			]
		] &,
		Select[
			tripleSplits[HoldComplete[args], Length[HoldComplete[left]], Length[HoldComplete[right]]],
			MatchQ[#[[2]], HoldComplete[__h]] &
		],
		n,
        SubstitutionSum
	]


(* BlankNullSequence *)

PatternSubstitutions[head_Symbol[args___], head_Symbol[left___, Verbatim[BlankNullSequence][h___], right___], n_] :=
	FoldTakeWhile[
		With[{valLeft = Unevaluated @@ head @@@ HoldComplete @@ {#[[1]]}, valRight = Unevaluated @@ head @@@ HoldComplete @@ {#[[3]]}},
			SubstitutionExpand[
				SubstitutionMerge[
                    If[ Length[HoldComplete[left]] > 0,
					    PartSubstitution[{1}, HoldPattern[head[left]], PatternSubstitutions[valLeft, Unevaluated[head[left]]]],
                        SubstitutionValues[]
                    ],
					PartSubstitution[{Length[HoldComplete[left]] + 1}, HoldPattern[BlankNullSequence[h]], HoldApply[Sequence, #[[2]], SubstitutionValues]],
                    If[ Length[HoldComplete[right]] > 0,
					    PartSubstitution[{Length[HoldComplete[left]] + 2}, HoldPattern[head[right]], PatternSubstitutions[valRight, Unevaluated[head[right]]]],
                        SubstitutionValues[]
                    ]
				],
				n
			]
		] &,
		Select[
			tripleSplits[HoldComplete[args], Length[HoldComplete[left]], Length[HoldComplete[right]]],
			MatchQ[#[[2]], HoldComplete[___h]] &
		],
		n,
        SubstitutionSum
	]


(* OrderlessPatternSequence *)

PatternSubstitutions[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[OrderlessPatternSequence][patt___], right___], n_] :=
    FoldTakeWhile[
        With[{
            valLeft = Unevaluated @@ head @@@ HoldComplete @@ {#[[1]]},
            valMid = #[[2]],
            valRight = Unevaluated @@ head @@@ HoldComplete @@ {#[[3]]}
        },
			SubstitutionExpand[
				SubstitutionMerge[
                    If[ Length[HoldComplete[left]] > 0,
					    PartSubstitution[{1}, HoldPattern[head[left]], PatternSubstitutions[valLeft, Unevaluated[head[left]]]],
                        SubstitutionValues[]
                    ],
                    PartSubstitution[
                        {Length[HoldComplete[left]] + 1},
                        HoldPattern[mid],
                        First @ NestWhile[
                            With[{val = Unevaluated @@ head @@@ HoldComplete @@ {valMid[[#[[2]]]]}},
                                {
                                    SubstitutionSum[#[[1]], PatternSubstitutions[val, Unevaluated @ head[patt], n]],
                                    ResourceFunction["NextPermutation"][#[[2]]]
                                }
                            ] &,
                            {SubstitutionSum[], Range[Length[valMid]]},
                            Length[#[[1]]] < n &,
                            1,
                            Min[Length[valMid] !, Infinity]
                        ]
                    ],
                    If[ Length[HoldComplete[right]] > 0,
					    PartSubstitution[{Length[HoldComplete[left]] + 2}, HoldPattern[head[right]], PatternSubstitutions[valRight, Unevaluated[head[right]]]],
                        SubstitutionValues[]
                    ]
				],
				n
			]
		] &,
        tripleSplits[HoldComplete[args], Length[HoldComplete[left]], Length[HoldComplete[right]]],
		n,
        SubstitutionSum
	]


(* PatternSequence *)

PatternSubstitutions[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[PatternSequence][patt___], right___], n_] :=
    FoldTakeWhile[
		With[{
            valLeft = Unevaluated @@ head @@@ HoldComplete @@ {#[[1]]},
            valMid = Unevaluated @@ head @@@ HoldComplete @@ {#[[2]]},
            valRight = Unevaluated @@ head @@@ HoldComplete @@ {#[[3]]}
        },
			SubstitutionExpand[
				SubstitutionMerge[
                    If[ Length[HoldComplete[left]] > 0,
					    PartSubstitution[{1}, HoldPattern[head[left]], PatternSubstitutions[valLeft, Unevaluated[head[left]]]],
                        SubstitutionValues[]
                    ],
					PartSubstitution[{Length[HoldComplete[left]] + 1}, HoldPattern[mid], PatternSubstitutions[valMid, Unevaluated[head[patt]]]],
                    If[ Length[HoldComplete[right]] > 0,
					    PartSubstitution[{Length[HoldComplete[left]] + 2}, HoldPattern[head[right]], PatternSubstitutions[valRight, Unevaluated[head[right]]]],
                        SubstitutionValues[]
                    ]
				],
				n
			]
		] &,
		tripleSplits[HoldComplete[args], Length[HoldComplete[left]], Length[HoldComplete[right]]],
		n,
        SubstitutionSum
	]


(* RepeatedNull *)

PatternSubstitutions[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[RepeatedNull][patt_, spec_ : Infinity], right___], n_] := Block[{
    shift = Length[HoldComplete[left]],
    min = Replace[spec, {{k_} :> k, {min_, _} :> min, _ -> 0}],
    max = Replace[spec, {{k_} :> k, {_, max_} :> max}],
    numRepeats,
    i = 0,
    rest
},
    numRepeats = max - min + 1;
	FoldTakeWhile[
        Apply[
        SubstitutionExpand[
            SubstitutionMerge[
                With[{val = Unevaluated @@ head @@@ HoldComplete[#1]}, PatternSubstitutions[val, Unevaluated[head[left]]]],
                PartSubstitution[{shift + 1},
                    HoldPattern[mid],
                    SubstitutionSum @@ NestWhile[
                        With[{
                            p = If[
                                i == 0,
                                Unevaluated @@ head @@@ HoldComplete @@ {Append[Flatten[HoldComplete @@ Table[HoldComplete[patt], min]], rest___]},
                                Unevaluated @@ {head[patt, rest___]}
                            ]
                        },
                            i++;
                            Map[
                                With[{
                                    prevSubst = #[[1]], len = Length[#[[2]]],
                                    val = Unevaluated @@ head @@@ HoldComplete @@ {#[[2]]}
                                },
                                    Which[
                                        (* input sequence is empty*)
                                        len == 0,
                                        {If[i == 1 && min > 0, SubstitutionSum[], prevSubst], #[[2]]},
                                        (* last iteration but input is not empty *)
                                        i == numRepeats + 1,
                                        {SubstitutionSum[], #[[2]]},
                                        True,
                                        Splice @ Block[{subst = SubstitutionExpand @ PatternSubstitutions[val, p]},
                                            With[{next = HoldComplete @@ Lookup[First @ SubstitutionBindings[#], rest, Null, Hold]},
                                                If[ Length[next] <= len,
                                                    {
                                                        SubstitutionProduct[
                                                            prevSubst,
                                                            (* replace with dummy sequence *)
                                                            # /. PartSubstitution[{2}, Verbatim[HoldPattern][Verbatim[Pattern][rest, _]], _] -> SubstitutionValues[Sequence[]]
                                                        ],
                                                        next
                                                    },
                                                    Nothing
                                                ]
                                            ] & /@ List @@ subst
                                        ]
                                    ]
                                ] &,
                                #
                            ]
                        ] &,
                        {{SubstitutionValues[], #2}},
                        i == 0 || AnyTrue[#[[All, 2]], Length[#] > 0 &] &,
                        1,
                        numRepeats,
                        1
                    ][[;; UpTo[n], 1]]
                ],
                With[{val = Unevaluated @@ head @@@ HoldComplete[#3]}, PatternSubstitutions[val, Unevaluated[head[right]]] /.
                    PartSubstitution[part_, rest__] :> PartSubstitution[Prepend[Rest[part], shift + 2], rest]]
            ],
            n
        ] &],
        tripleSplits[HoldComplete[args], Length[HoldComplete[left]], Length[HoldComplete[right]]],
        n,
        SubstitutionSum
    ]
]


(* Repeated *)

PatternSubstitutions[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[Repeated][patt_, spec_ : Infinity], right___], n_] := With[{
    newSpec = Replace[spec, {k : Except[_List] :> {1, k}}]
},
    PatternSubstitutions[Unevaluated[head[args]], Unevaluated[head[left, RepeatedNull[patt, newSpec], right]], n]
]


(* HoldPattern *)

PatternSubstitutions[expr_, Verbatim[HoldPattern][patt_], n_] := PatternSubstitutions[Unevaluated[expr], Unevaluated[patt], n]


(* Verbatim *)

PatternSubstitutions[expr_, Verbatim[Verbatim][expr_], _] := SubstitutionValues[]


(* Except *)

PatternSubstitutions[expr_, Verbatim[Except][patt_, t___], n_] := With[{
	subst = PatternSubstitutions[Unevaluated[expr], Unevaluated[patt], 1]
},
	If[ subst === SubstitutionSum[],
		SubstitutionProduct[
            DefaultSubstitutions[Unevaluated[patt]],
            If[ HoldComplete[t] === HoldComplete[],
                SubstitutionValues[expr],
                PatternSubstitutions[Unevaluated[expr], Unevaluated[t], n]
            ]
        ],
		SubstitutionSum[]
	]
]


PatternSubstitutions[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[Except][patt_, t___], right___], n_] := With[{shift = Length[HoldComplete[left]]},
	SubstitutionExpand[
		SubstitutionSum @@ Apply[SubstitutionMerge[
			With[{val = Unevaluated @@ head @@@ HoldComplete[#1]}, PatternSubstitutions[val, Unevaluated[head[left]]]],
			PartSubstitution[{shift + 1},
				HoldPattern[mid],
				With[{val = Unevaluated @@ head @@@ HoldComplete[#2]},
                    With[{
                        subst = PatternSubstitutions[val, Unevaluated[head[patt]], 1]
                    },
                        If[ subst === SubstitutionSum[],
                            SubstitutionProduct[
                                DefaultSubstitutions[Unevaluated[head[patt]]],
                                If[ HoldComplete[t] === HoldComplete[],
                                    SubstitutionValues @@ #2,
                                    PatternSubstitutions[val, Unevaluated[head[t]], n]
                                ]
                            ],
                            SubstitutionSum[]
                        ]
                    ]
                ] /. PartSubstitution[part_, rest__] :> PartSubstitution[Rest[part], rest]
			],
			With[{val = Unevaluated @@ head @@@ HoldComplete[#3]}, PatternSubstitutions[val, Unevaluated[head[right]]] /. PartSubstitution[part_, rest__] :> PartSubstitution[Prepend[Rest[part], shift + 2], rest]]
		] &] /@ tripleSplits[HoldComplete[args], Length[HoldComplete[left]], Length[HoldComplete[right]]],
		n
	]
]


(* Alternatives *)

PatternSubstitutions[expr_, Verbatim[Alternatives][alts___], n_] :=
    FoldTakeWhile[
        Function[alt, PartSubstitution[{}, HoldPattern[alt], PatternSubstitutions[Unevaluated[expr], Unevaluated[alt], n]], HoldAllComplete],
        HoldComplete[alts],
        n,
        SubstitutionSum
    ]

PatternSubstitutions[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[Alternatives][alts___], right___], n_] := With[{shift = Length[HoldComplete[left]]},
	SubstitutionExpand[
		SubstitutionSum @@ Apply[SubstitutionMerge[
			With[{val = Unevaluated @@ head @@@ HoldComplete[#1]}, PatternSubstitutions[val, Unevaluated[head[left]]]],
			PartSubstitution[{shift + 1},
				HoldPattern[mid],
				With[{val = Unevaluated @@ head @@@ HoldComplete[#2]},
                    FoldTakeWhile[
                        Function[alt, PartSubstitution[{}, HoldPattern[alt],
                            PatternSubstitutions[val, Unevaluated[head[alt]], n] /. PartSubstitution[part_, rest__] :> PartSubstitution[Rest[part], rest]], HoldAllComplete],
                        HoldComplete[alts],
                        n,
                        SubstitutionSum
                    ]
                ]
			],
			With[{val = Unevaluated @@ head @@@ HoldComplete[#3]}, PatternSubstitutions[val, Unevaluated[head[right]]] /. PartSubstitution[part_, rest__] :> PartSubstitution[Prepend[Rest[part], shift + 2], rest]]
		] &] /@ tripleSplits[HoldComplete[args], Length[HoldComplete[left]], Length[HoldComplete[right]]],
		n
	]
]


(* Optional *)

PatternSubstitutions[expr_, Verbatim[Optional][patt_, def___], n_] := SubstitutionSum[
    PatternSubstitutions[Unevaluated[expr], Unevaluated[patt], n],
    PartSubstitution[
        {},
        Replace[HoldPattern[patt], Verbatim[HoldPattern][Verbatim[Optional][p_Pattern, ___]] :> HoldPattern[p]],
        If[HoldComplete[def] === HoldComplete[], SubstitutionValues[Sequence[]], SubstitutionValues[def]]
    ]
]


PatternSubstitutions[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[Optional][patt_, def___], right___], n_] := With[{shift = Length[HoldComplete[left]]},
	SubstitutionExpand[SubstitutionSum @@ Map[Apply[
        Block[{
            lsubst = If[Length[HoldComplete[left]] > 0,
                With[{val = Unevaluated @@ head @@@ HoldComplete[#1]}, PatternSubstitutions[val, Unevaluated[head[left]]]],
                SubstitutionValues[]
            ],
            nsubst, rsubst
        },
            (* negative case *)
            nsubst = If[
                lsubst === SubstitutionSum[],
                SubstitutionSum[],
                PartSubstitution[
                    {shift + 1},
                    Replace[HoldPattern[mid], Verbatim[HoldPattern][Verbatim[Optional][p_Pattern, ___]] :> HoldPattern[p]],
                    DefaultSubstitutions[Unevaluated[patt]]
                ]
            ];
            rsubst = Which[
                Length[HoldComplete[right]] > 0,
                SubstitutionValues[],
                nsubst === SubstitutionSum[],
                SubstitutionSum[],
                True,
                With[{val = Unevaluated @@ head @@@ HoldComplete[#3]}, PatternSubstitutions[val, Unevaluated[head[right]]]] /.
                    PartSubstitution[part_, rest__] :> PartSubstitution[Prepend[Rest[part], shift + 2], rest]
            ];
            With[{
                val = Unevaluated @@ head @@@ HoldComplete[#2]
            },
            With[{
                posSubst = (* positive case *)
                    SubstitutionExpand[
                        SubstitutionMerge[
                            lsubst,
                            PartSubstitution[
                                {shift + 1},
                                Replace[HoldPattern[mid], Verbatim[HoldPattern][Verbatim[Optional][p_Pattern, ___]] :> HoldPattern[p]],
                                SubstitutionSum[
                                    PatternSubstitutions[val, Unevaluated[head[patt]]] /. PartSubstitution[part_, rest__] :> PartSubstitution[Rest[part], rest],
                                    If[HoldComplete[def] =!= HoldComplete[], SubstitutionValues[def], SubstitutionSum[]]
                                ]
                            ],
                            rsubst
                        ],
                        n
                    ]
            },
                SubstitutionSum[
                    posSubst,
                    If[ Length[posSubst] >= n,
                        SubstitutionSum[],
                        SubstitutionProduct[lsubst, nsubst, rsubst]
                    ]
                ]
            ]]
        ] &],
		    tripleSplits[HoldComplete[args], Length[HoldComplete[left]], Length[HoldComplete[right]]]
	    ],
        n
    ]
]


(* Condition *)

PatternSubstitutions[expr_, Verbatim[Condition][patt_, cond_], n_] :=
	Select[SubstitutionExpand @ PatternSubstitutions[Unevaluated[expr], Unevaluated[patt]], ReplaceAll[Unevaluated[cond], First @ SubstitutionBindings[#]] &, n]


(* PatternTest *)

PatternSubstitutions[expr_, Verbatim[PatternTest][patt_, test_], n_] :=
	Select[SubstitutionExpand @ PatternSubstitutions[Unevaluated[expr], Unevaluated[patt]], test[ReleaseHold @ First @ SubstitutionApply[Unevaluated[patt], #]] &, n]


(* OptionsPattern/KeyValuePattern *)

PackageExport["SubsetPatternSequence"]

PatternSubstitutions[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[SubsetPatternSequence][patt___], right___], n_] := With[{shift = Length[HoldComplete[left]]},
    SubstitutionExpand[
		SubstitutionSum @@ Apply[SubstitutionMerge[
			With[{val = Unevaluated @@ head @@@ HoldComplete[#1]}, PatternSubstitutions[val, Unevaluated[head[left]]]],
			PartSubstitution[{shift + 1},
				HoldPattern[mid],
                Function[arg, PatternSubstitutions[arg] /@ Unevaluated[patt], HoldAll] /@ #2
			],
			With[{val = Unevaluated @@ head @@@ HoldComplete[#3]}, PatternSubstitutions[val, Unevaluated[head[right]]] /. PartSubstitution[part_, rest__] :> PartSubstitution[Prepend[Rest[part], shift + 2], rest]]
		] &] /@ tripleSplits[HoldComplete[args], Length[HoldComplete[left]], Length[HoldComplete[right]]],
		n
	]
]

(* fallback *)

PatternSubstitutions[head1_[args___], head2_[patt___], n_] /; Length[Unevaluated[{args}]] == Length[Unevaluated[{patt}]] := With[{
    headSubst = If[
        Unevaluated[head1] === Unevaluated[head2],
        SubstitutionValues[],
        SubstitutionExpand[PatternSubstitutions[Unevaluated[head1], Unevaluated[head2], n]]
    ]
},
    SubstitutionMerge[
        headSubst /. PartSubstitution[part_, rest__] :> PartSubstitution[Prepend[part, 0], rest],
        SubstitutionProduct @@ Catch @ MapThread[
            With[{e = Unevaluated @@ #1, p = Unevaluated @@ #2},
                With[{subst = PatternSubstitutions[e, p, Ceiling[n / Length[headSubst]]]},
                    If[ subst === SubstitutionSum[],
                        Throw[{subst}],
                        subst /. PartSubstitution[part_, rest__] :> PartSubstitution[Prepend[part, #3], rest]
                    ]
                ]
            ] &,
            {HoldComplete /@ Unevaluated[{args}], HoldComplete /@ Unevaluated[{patt}], Range[Length[Unevaluated[{args}]]]}
        ]
    ]
]


PatternSubstitutions[head_Symbol[args___], head_Symbol[patt___], n_] /; MemberQ[Attributes[head], Flat] := Block[{h},
    SetAttributes[h, DeleteCases[Attributes[head], Flat]];
    SubstitutionProduct @@ (
        With[{expr = Unevaluated @@ #1, p = Unevaluated @@ #2}, PatternSubstitutions[expr, p, n]] & @@@
            Tuples[{Groupings[Unevaluated[{args}], {{h -> 1, 1}, h -> 2}, Hold], Groupings[Unevaluated[{patt}], {{h -> 1, 1}, h -> 2}, Hold]}]
    ) /. h :> head
]


PatternSubstitutions[expr_, Unevaluated[Sequence[]], _] := SubstitutionValues[expr]

PatternSubstitutions[expr_, expr_, _] := PartSubstitution[{}, HoldPattern[expr], SubstitutionValues[expr]]

PatternSubstitutions[___] := SubstitutionSum[]

