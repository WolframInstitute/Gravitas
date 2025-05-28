Package["WolframInstitute`Gravitas`ShapedTensor`"]

PackageImport["WolframInstitute`Gravitas`ShapedTensor`TensorUtilities`"]

PackageExport[ShapedTensorQ]
PackageExport[ShapedTensor]



ClearAll[shapedTensorQ, ShapedTensorQ, ShapedTensor, Prop]

(* Validation *)

shapedTensorQ[ShapedTensor[tensor_, shape_Shape ? ShapeQ, params_List, assumptions_List, ___]] :=
    DeleteCases[Assuming[assumptions, tensorDimensions[tensor]], 0] === DeleteCases[shape["Dimensions"], 0]

shapedTensorQ[___] := False


ShapedTensorQ[st_ShapedTensor] := System`Private`HoldValidQ[st] || shapedTensorQ[Unevaluated[st]]

ShapedTensorQ[___] := False


(* Mutation *)

ShapedTensor[st_ ? ShapedTensorQ, arg1_, arg2_, args___] := With[{shape = Shape[arg1]},
    Which[
        ShapeQ[shape],
        ShapedTensor[ShapedTensor[st["Tensor"], shape, st["Parameters"], st["Assumptions"], st["Name"]], arg2, args],
        MatchQ[arg1, _List] && MatchQ[arg2, _List],
        ShapedTensor[st["Tensor"], st["Shape"], arg1, arg2, st["Name"]],
        MatchQ[arg1, _List],
        ShapedTensor[st["Tensor"], st["Shape"], arg1, st["Assumptions"], arg2, args],
        True,
        ShapedTensor[st["Tensor"], st["Shape"], st["Parameters"], st["Assumptions"], arg1, arg2, args]
    ]
]

ShapedTensor[st_ ? ShapedTensorQ, arg_] := With[{shape = Shape[arg]},
    Which[
        ShapeQ[shape],
        ShapedTensor[st["Tensor"], shape, st["Parameters"], st["Assumptions"], st["Name"]],
        MatchQ[arg, _List],
        ShapedTensor[st["Tensor"], st["Shape"], arg, st["Assumptions"], st["Name"]],
        True,
        ShapedTensor[st["Tensor"], st["Shape"], st["Parameters"], st["Assumptions"], arg]
    ]
]

ShapedTensor[st_ShapedTensor] := st


(* Constructors *)

ShapedTensor[tensor_, variance : {__ ? BooleanQ}, args___] :=    
    ShapedTensor[tensor, # * PadRight[- (-1) ^ Boole[variance], Length[#], 1] & @ ShapedTensor[tensor]["Dimensions"], args]

ShapedTensor[tensor_, Longest[variance : __ ? BooleanQ], args___] := ShapedTensor[tensor, {variance}, args]

ShapedTensor[tensor_, shape_Shape ? ShapeQ] := ShapedTensor[tensor, shape, {}, {}]

ShapedTensor[tensor_, shape_Shape ? ShapeQ, params_List] := ShapedTensor[tensor, shape, params, {}]

ShapedTensor[tensor_, shape_Shape ? ShapeQ, name : Except[_List]] :=
    ShapedTensor[tensor, shape, {}, {}, name]


st_ShapedTensor /; System`Private`HoldNotValidQ[st] && shapedTensorQ[Unevaluated[st]] :=
    System`Private`SetNoEntry[System`Private`HoldSetValid[st]]



(* Properties *)

(m_ShapedTensor ? ShapedTensorQ)[prop_String | prop_String[args___]] /; MemberQ[ShapedTensor["Properties"], prop] := Prop[m, prop, args]

ShapedTensor["Properties"] := Union @ Join[
    {
        "Properties", "Tensor", "Shape", "Parameters", "Assumptions", "Name", "Dimension", "Symmetry", "Symbol", "Icon"
    },
    Shape["Properties"]
]

Prop[_, "Properties"] := ShapedTensor["Properties"]

Prop[ShapedTensor[tensor_, ___], "Tensor"] := tensor

Prop[ShapedTensor[_, shape_, ___], "Shape"] := shape

Prop[ShapedTensor[_, _, params_, ___], "Parameters"] := params

Prop[ShapedTensor[_, _, _, assumptions_, ___], "Assumptions"] := DeleteCases[assumptions, _ ? BooleanQ]

Prop[ShapedTensor[_, _, _, _, name_, ___], "Name"] := name

Prop[st_, "Name"] := tensorName[st["Tensor"]]


Prop[st_, "Dimension"] := Times @@ st["Dimensions"]

Prop[st_, "Symmetry"] := TensorSymmetry[st["Tensor"]]


Prop[st_, "Symbol"] := Row[{
    Tooltip[Replace[st["Name"], None -> \[FormalCapitalT]], st["SignedDimensions"]],
    Splice @ Map[
        With[{index = #["Index"]}, {dim = #["SignedDimension"], name = If[MissingQ[index], #["Name"], index]},
        Tooltip[
            Which[
                dim > 0, Superscript["", name],
                dim < 0, Subscript["", name],
                True, Superscript["", Style[name, Opacity[.3]]]
            ],
            #["View"]
        ]
    ] &,
    st["Shape"]["Indices"]
    ]
}]
   

squareDimensions[d_, limit_ : 10] := With[{w = Floor[Sqrt[d]]}, Clip[{w, If[w == 0, 0, d / w]}, {1, limit}]]

Prop[st_, "Icon", limit_Integer : 10] := MatrixPlot[
    Map[
        Replace[{x_ ? (Not @* NumericQ) :> BlockRandom[RandomComplex[], RandomSeeding -> Hash[x]], x_ :> N[x]}],
        Replace[
            st["Tensor"],
            {
                m_ ? MatrixQ :> m[[;; UpTo[limit], ;; UpTo[limit]]],
                t_ ? ArrayQ :> ArrayReshape[t, squareDimensions[st["Dimension"], limit]],
                _ :> BlockRandom[RandomReal[{-1, 1}, squareDimensions[st["Dimension"], limit]], RandomSeeding -> Hash[st]]
            }
        ],
        {2}
    ],
    ImageSize -> Dynamic[{Automatic, 3.5 * (CurrentValue["FontCapHeight"] / AbsoluteCurrentValue[Magnification])}],
    Frame -> False,
    FrameTicks -> None
]

Prop[st_, prop_String] /; MemberQ[Shape["Properties"], prop] := st["Shape"][prop]

Prop[_, prop_String, ___] := Missing[prop]


(* UpValues *)

ShapedTensor /: Normal[st_ShapedTensor ? ShapedTensorQ] := st["Tensor"]


(* General fallback *)

st : ShapedTensor[t_, arg_, params_, assumptions_List, args___] /; ! ShapedTensorQ[Unevaluated[st]] := With[{shape = Shape[arg], dims = Assuming[assumptions, tensorDimensions[t]]},
    If[ ShapeQ[shape],
        ShapedTensor[If[dims === shape["Dimensions"], t, setDimensions[t, shape["Dimensions"]]], shape, params, assumptions, args],
        ShapedTensor[t, dims, params, assumptions, args]
    ]
]

st : ShapedTensor[t_, arg_, params_, name_, args___] /; ! ShapedTensorQ[Unevaluated[st]] := ShapedTensor[t, arg, params, {}, name, args]

st : ShapedTensor[t_, arg_, args___] /; ! ShapedTensorQ[Unevaluated[st]] := With[{shape = Shape[arg]},
    If[ ShapeQ[shape],
        ShapedTensor[If[tensorDimensions[t] === shape["Dimensions"], t, setDimensions[t, shape["Dimensions"]]], shape, args],
        ShapedTensor[t, tensorDimensions[t], arg, args]
    ]
]

ShapedTensor[t_] := ShapedTensor[t, tensorDimensions[t]]


(* Index juggling *)

st_ShapedTensor[is : (_Integer | All) ..] := With[{indices = st["Indices"]},
    ShapedTensor[
        tensorPart[st["Tensor"], {is}],
        MapThread[
            If[IntegerQ[#2], Dimension[#1, Mod[#2, #1["Dimension"], 1]], #1] &, 
            {indices, ReplacePart[indices, Thread[Take[Select[indices, ! #["IndexQ"] & -> "Index"], UpTo[Length[{is}]]] -> {is}]]}
        ],
        st["Parameters"], st["Assumptions"], st["Name"]
    ]
]

st_ShapedTensor[] := st

st_ShapedTensor[is__] := Block[{indices = st["Indices"], names, repl, perm, renames},
    names = PositionIndex[Through[indices["Name"]]];
    repl = MapIndexed[Lookup[names, Key[CanonicalSymbolName[#1]], Missing[#2]] -> #2 &, {is}];
    perm = FindPermutation @ Map[If[MissingQ[#], Replace[repl] @ Replace[repl] @ First[#], #] &, repl[[All, 1]]];
    renames = Cases[repl, (Missing[k_] -> _) :> k -> Extract[{is}, k]];
    ShapedTensor[
        tensorTranspose[st["Tensor"], perm],
        SubsetMap[MapThread[Dimension, {#, renames[[All, 2]]}] &, Permute[indices, perm], renames[[All, 1]]],
        st["Parameters"], st["Assumptions"], st["Name"]
    ]
]


(* Formatting *)

ShapedTensor /: MakeBoxes[st_ShapedTensor /; ShapedTensorQ[Unevaluated[st]], TraditionalForm] := With[{
    boxes = ToBoxes[Style[st["Symbol"], "ShowStringCharacters" -> False], TraditionalForm]
},
    InterpretationBox[
        boxes,
        st
    ]
]

ShapedTensor /: MakeBoxes[st_ShapedTensor /; ShapedTensorQ[Unevaluated[st]], form_] := 
    BoxForm`ArrangeSummaryBox["ShapedTensor", st, st["Icon"],
        {
            {
                BoxForm`SummaryItem[{"Symbol: ", st["Symbol"]}],
                BoxForm`SummaryItem[{"Dimensions: ", st["Dimensions"]}]
            },
            {
                BoxForm`SummaryItem[{"Parameters: ", st["Parameters"]}],
                BoxForm`SummaryItem[{"Assumptions: ", st["Assumptions"]}]
            }
        },
        {
            
        },
        form,
        "Interpretable" -> Automatic
    ]
    
