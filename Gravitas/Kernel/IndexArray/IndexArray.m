Package["WolframInstitute`Gravitas`IndexArray`"]

PackageImport["WolframInstitute`Gravitas`IndexArray`TensorUtilities`"]
PackageImport["WolframInstitute`Gravitas`Utilities`"]

PackageExport[IndexArrayQ]
PackageExport[IndexArray]



ClearAll[IndexArrayQ, IndexArray, Prop]

(* Validation *)

indexArrayQ[IndexArray[tensor_, shape_Shape ? ShapeQ, params_List, assumptions_List, ___]] :=
    DeleteCases[Assuming[assumptions, tensorDimensions[tensor]], 0] === DeleteCases[shape["Dimensions"], 0]

indexArrayQ[___] := False


IndexArrayQ[ia_IndexArray] := System`Private`HoldValidQ[ia] || indexArrayQ[Unevaluated[ia]]

IndexArrayQ[___] := False


(* Mutation *)

IndexArray[ia_ ? IndexArrayQ, arg1_, arg2_, args___] := With[{shape = Shape[arg1]},
    Which[
        ShapeQ[shape],
        IndexArray[IndexArray[ia["Tensor"], shape, ia["Parameters"], ia["Assumptions"], ia["Name"]], arg2, args],
        MatchQ[arg1, _List] && MatchQ[arg2, _List],
        IndexArray[ia["Tensor"], ia["Shape"], arg1, arg2, args, ia["Name"]],
        MatchQ[arg1, _List],
        IndexArray[ia["Tensor"], ia["Shape"], arg1, ia["Assumptions"], arg2, args],
        True,
        IndexArray[ia["Tensor"], ia["Shape"], ia["Parameters"], ia["Assumptions"], arg1, arg2, args]
    ]
]

IndexArray[ia_ ? IndexArrayQ, arg_] := With[{shape = Shape[arg]},
    Which[
        ShapeQ[shape],
        IndexArray[ia["Tensor"], shape, ia["Parameters"], ia["Assumptions"], ia["Name"]],
        MatchQ[arg, _List],
        IndexArray[ia["Tensor"], ia["Shape"], arg, ia["Assumptions"], ia["Name"]],
        True,
        IndexArray[ia["Tensor"], ia["Shape"], ia["Parameters"], ia["Assumptions"], arg]
    ]
]

IndexArray[ia_IndexArray] := ia


(* Constructors *)

IndexArray[tensor_, variance : {__ ? BooleanQ}, args___] :=    
    IndexArray[tensor, # * PadRight[- (-1) ^ Boole[variance], Length[#], 1] & @ IndexArray[tensor]["Dimensions"], args]

IndexArray[tensor_, Longest[variance : __ ? BooleanQ], args___] := IndexArray[tensor, {variance}, args]

IndexArray[tensor_, shape_Shape ? ShapeQ] := IndexArray[tensor, shape, {}, {}]

IndexArray[tensor_, shape_Shape ? ShapeQ, params_List] := IndexArray[tensor, shape, params, {}]

IndexArray[tensor_, shape_Shape ? ShapeQ, name : Except[_List]] := IndexArray[tensor, shape, {}, {}, name]


ia_IndexArray /; System`Private`HoldNotValidQ[ia] && IndexArrayQ[Unevaluated[ia]] :=
    System`Private`SetNoEntry[System`Private`HoldSetValid[ia]]



(* Properties *)

(m_IndexArray ? IndexArrayQ)[prop_String | prop_String[args___]] /; MemberQ[IndexArray["Properties"], prop] := Prop[m, prop, args]

IndexArray["Properties"] := Union @ Join[
    {
        "Properties", "Array", "Tensor", "Shape", "Parameters", "Assumptions", "Name", "Dimension", "Symmetry", "Symbol", "Icon"
    },
    Shape["Properties"]
]

Prop[_, "Properties"] := IndexArray["Properties"]

Prop[IndexArray[array_, ___], "Array" | "Tensor"] := array

Prop[IndexArray[_, shape_, ___], "Shape"] := shape

Prop[IndexArray[_, _, params_, ___], "Parameters"] := params

Prop[IndexArray[_, _, _, assumptions_, ___], "Assumptions"] := DeleteCases[assumptions, _ ? BooleanQ]

Prop[IndexArray[_, _, _, _, name_, ___], "Name"] := name

Prop[ia_, "Name"] := tensorName[ia["Array"]]


Prop[ia_, "Dimension"] := Times @@ ia["Dimensions"]

Prop[ia_, "Symmetry"] := tensorSymmetry[ia["Array"]]


Prop[ia_, "Symbol"] := With[{
    indices = Map[
        With[{dim = #["SignedDimension"], name = #["IndexName"]},
            Tooltip[
                Which[
                    dim > 0, Superscript["", name],
                    dim < 0, Subscript["", name],
                    True, Superscript["", Style[name, Opacity[.3]]]
                ],
                #["View"]
            ]
        ] &,
        ia["Shape"]["Indices"]
    ],
    name = ia["Name"]
},
    If[ MatchQ[name, _Function],
        name @@ indices,
        Row[{
            Tooltip[Replace[name, None -> \[FormalCapitalT]], ia["SignedDimensions"]],
            Splice @ indices
        }]
    ]
]
   

squareDimensions[d_, limit_ : 10] := With[{w = Floor[Sqrt[d]]}, Clip[{w, If[w == 0, 0, Ceiling[d / w]]}, {1, limit}]]

Prop[ia_, "Icon", limit_Integer : 10] := MatrixPlot[
    Map[
        Replace[{x_ ? (Not @* NumericQ) :> BlockRandom[RandomComplex[], RandomSeeding -> Hash[x]], x_ :> N[x]}],
        Replace[
            Normal[ia["Array"]],
            {
                v_ ? VectorQ :> If[ia["SignedDimensions"][[1]] > 0, Map[List], List] @ v[[;; UpTo[limit]]],
                m_ ? MatrixQ :> m[[;; UpTo[limit], ;; UpTo[limit]]],
                t_ ? ArrayQ :> ArrayReshape[t, squareDimensions[ia["Dimension"], limit]],
                _ :> BlockRandom[RandomReal[{-1, 1}, squareDimensions[ia["Dimension"], limit]], RandomSeeding -> Hash[ia]]
            }
        ],
        {2}
    ],
    ImageSize -> Dynamic[{Automatic, 3.5 * (CurrentValue["FontCapHeight"] / AbsoluteCurrentValue[Magnification])}],
    Frame -> False,
    FrameTicks -> None
]

Prop[ia_, prop_String] /; MemberQ[Shape["Properties"], prop] := ia["Shape"][prop]

Prop[_, prop_String, ___] := Missing[prop]


(* UpValues *)

applyIndexArray[f_, ia_IndexArray ? IndexArrayQ] := IndexArray[f[ia["Array"]], ia["Shape"], ia["Parameters"], ia["Assumptions"], ia["Name"]]

IndexArray /: Normal[ia_IndexArray ? IndexArrayQ] := Normal[ia["Tensor"]]

IndexArray /: Dimensions[ia_IndexArray ? IndexArrayQ] := ia["Dimensions"]

IndexArray /: SquareMatrixQ[ia_IndexArray ? IndexArrayQ] := MatchQ[Dimensions[ia], {x_, x_}]

IndexArray /: Inverse[ia_IndexArray ? IndexArrayQ] /; SquareMatrixQ[ia] := IndexArray[
    Inverse[Normal[ia["Tensor"]]],
    Minus /@ ia["Shape"],
    ia["Parameters"],
    ia["Assumptions"],
    ia["Name"]
]

IndexArray /: D[ia_IndexArray ? IndexArrayQ, x_] := applyIndexArray[D[#, x] &, ia]


(* General fallback *)

ia : IndexArray[t_, arg_, params_, assumptions_List, args___] /; ! IndexArrayQ[Unevaluated[ia]] := With[{shape = Shape[arg], dims = Assuming[assumptions, tensorDimensions[t]]},
    If[ ShapeQ[shape],
        IndexArray[If[dims === shape["Dimensions"], t, setDimensions[t, shape["Dimensions"]]], shape, ToList[params], assumptions, args],
        IndexArray[t, Shape[dims, arg], ToList[params], assumptions, args]
    ]
]

ia : IndexArray[t_, arg_, params_, name_, args___] /; ! IndexArrayQ[Unevaluated[ia]] := IndexArray[t, arg, params, {}, name, args]

ia : IndexArray[t_, arg_, args___] /; ! IndexArrayQ[Unevaluated[ia]] := With[{shape = Shape[arg]},
    If[ ShapeQ[shape],
        IndexArray[If[tensorDimensions[t] === shape["Dimensions"], t, setDimensions[t, shape["Dimensions"]]], shape, args],
        With[{argShape = Shape[tensorDimensions[t], arg]}, If[ShapeQ[argShape], IndexArray[t, argShape, args], IndexArray[t, Shape[tensorDimensions[t]], arg, args]]]
    ]
]

IndexArray[t_] := IndexArray[t, tensorDimensions[t]]

(* ia : IndexArray[_, shape_, args___] /; ! IndexArrayQ[Unevaluated[ia]] := Which[
    ! ShapeQ[shape],
    Failure["IndexArray", <|"MessageTemplate" -> "Wrong shape specification: ``", "MessageParameters" -> {shape}|>]
    ,
    True,
    Failure["IndexArray", <|"MessageTemplate" -> "Failed to construct ``", "MessageParameters" -> HoldForm[ia]|>]
] *)


(* Index juggling *)

ia_IndexArray[[is__]] ^:= With[{indices = ia["Indices"]}, {
    js = MapThread[If[MatchQ[#2, _Integer | All], #2, Lookup[#1, Key[#2]]] &, {Map[First] @* PositionIndex /@ Through[Take[indices, UpTo[Length[{is}]]]["Indices"]], {is}}]
},
    IndexArray[
        tensorPart[ia["Array"], Replace[js, _Missing -> All, 1]],
        MapThread[
            If[ IntegerQ[#2],
                Dimension[#1, Mod[#2, #1["Dimension"], 1]],
                Replace[#2, {
                    Missing[_, - name_] :> Dimension[#1, name]["Lower"],
                    Missing[_, name_] :> Dimension[#1, name]["Upper"]
                }]
            ] &, 
            {indices, ReplacePart[indices, Thread[Take[Select[indices, (#["FreeQ"] &) -> "Index"], UpTo[Length[js]]] -> js]]}
        ],
        ia["Parameters"], ia["Assumptions"], ia["Name"]
    ] /; AnyTrue[js, IntegerQ]
]

ia_IndexArray[[]] ^:= ia

ia_IndexArray[rules : (_Integer -> _) ..] := With[{r = ia["Rank"]}, ia[[##]] & @@ ReplacePart[ConstantArray[All, r], Cases[{rules}, (k_ -> _) /; 0 < k <= r]]]


(ia : _IndexArray ? IndexArrayQ)[is___] := WolframInstitute`Gravitas`IndexJuggling[ia, {is}]


(* Formatting *)

IndexArray /: MakeBoxes[ia_IndexArray /; IndexArrayQ[Unevaluated[ia]], TraditionalForm] := With[{
    boxes = ToBoxes[Style[ia["Symbol"], "ShowStringCharacters" -> False], TraditionalForm]
},
    InterpretationBox[
        boxes,
        ia
    ]
]

IndexArray /: MakeBoxes[ia_IndexArray /; IndexArrayQ[Unevaluated[ia]], form_] := 
    BoxForm`ArrangeSummaryBox["IndexArray", ia, ia["Icon"],
        {
            {
                BoxForm`SummaryItem[{"Symbol: ", ia["Symbol"]}],
                BoxForm`SummaryItem[{"Dimensions: ", ia["Dimensions"]}]
            },
            {
                BoxForm`SummaryItem[{"Parameters: ", ia["Parameters"]}]
            }
        },
        {
            {
                BoxForm`SummaryItem[{"Symmetry: ", ia["Symmetry"]}],
                BoxForm`SummaryItem[{"Assumptions: ", ia["Assumptions"]}]
            }
        },
        form,
        "Interpretable" -> Automatic
    ]
    
