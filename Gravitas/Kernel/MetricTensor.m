Package["WolframInstitute`Gravitas`"]

PackageImport["WolframInstitute`Gravitas`ShapedTensor`"]

PackageExport[MetricTensorQ]
PackageExport[MetricTensor]


ClearAll[MetricTensor]
ClearAll[Prop]

(* Validation *)

metricTensorQ[MetricTensor[st_ShapedTensor]] :=
    ShapedTensorQ[st] &&
    MatchQ[st["Dimensions"], {n_, n_}]

metricTensorQ[___] := False


MetricTensorQ[mt_MetricTensor] := System`Private`HoldValidQ[mt] || metricTensorQ[Unevaluated[mt]]

MetricTensorQ[___] := False


(* Built-in metrics *)

MetricTensor[] := {
    "Symmetric", "SymmetricField", "Asymmetric", "AsymmetricField",
    "Euclidean", "Minkowski", 
    "Schwarzschild", "IsotropicSchwarzschild",
    "EddingtonFinkelstein", "IngoingEddingtonFinkelstein", "OutgoingEddingtonFinkelstein",
    "GullstrandPainleve", "IngoingGullstrandPainleve", "OutgoingGullstrandPainleve", 
    "KruskalSzekeres", "Kerr", "ReissnerNordstrom", "KerrNewman", "Godel", "FLRW"
}

t = \[FormalT]
x = \[FormalX]
y = \[FormalY]
z = \[FormalZ]
r = \[FormalR]
T = \[FormalCapitalT]
X = \[FormalCapitalX]
theta = \[FormalTheta]
phi = \[FormalPhi]
M = \[FormalCapitalM]
Q = \[FormalCapitalQ]
J = \[FormalCapitalJ]
k = \[FormalK]
a = \[FormalA]
sqrt2 = \[Sqrt]2
omega = \[FormalOmega]
u = \[FormalU]
v = \[FormalV]

g = \[FormalG]
mu = \[FormalMu]
nu = \[FormalNu]


padCoordinates[coordinates_List, d_Integer ? Positive] := PadRight[Join[coordinates, Superscript[x, #] & /@ Range[d - Length[coordinates]]], d]

padCoordinates[Automatic, d_] := padCoordinates[{}, d]


(* Symmetric *)

MetricTensor["Symmetric"[d : _Integer ? Positive : 4], args___] := 
    MetricTensor[
        SymmetrizedArray[(# -> Subscript[g, #] &) /@ Select[Tuples[Range[d], 2], OrderedQ], {d, d}, Symmetric[{1, 2}]],
        args
    ]


(* SymmetricField *)

MetricTensor["SymmetricField"[d : _Integer ? Positive : 4], coordinates_ : Automatic, args___] := With[{
    xs = padCoordinates[coordinates, d]
},
    MetricTensor[
        SymmetrizedArray[(# -> Subscript[g, #] @@ xs &) /@ Select[Tuples[Range[d], 2], OrderedQ], {d, d}, Symmetric[{1, 2}]],
        xs,
        args
    ]
]


(* Asymmetric *)

MetricTensor["Asymmetric"[d : _Integer ? Positive : 4], args___] := 
    MetricTensor[
        SymmetrizedArray[(# -> Subscript[g, #] &) /@ Subsets[Range[d], {2}], {d, d}, Antisymmetric[{1, 2}]],
        args
    ]


(* AsymmetricField *)

MetricTensor["AsymmetricField"[d : _Integer ? Positive : 4], coordinates_ : Automatic, args___] :=  With[{
    xs = padCoordinates[coordinates, d]
},
    MetricTensor[
        SymmetrizedArray[(# -> Subscript[g, #] @@ xs &) /@ Subsets[Range[d], {2}], {d, d}, Antisymmetric[{1, 2}]],
        xs,
        args
    ]
]

(* Euclidean *)

MetricTensor["Euclidean"[d : _Integer ? Positive : 3], args___] := 
    MetricTensor[DiagonalMatrix[ConstantArray[1, d]], args]


(* Minkowski *)

MetricTensor["Minkowski"[d : _Integer ? Positive : 4], coordinates_ : Automatic, args___] := 
    MetricTensor[
        DiagonalMatrix[Join[{-1}, ConstantArray[1, d - 1]]],
        Replace[coordinates, Automatic :> Join[{t}, Superscript[x, #] & /@ Range[d - 1]]],
        args
    ]


(* Schwarzschild *)

MetricTensor["Schwarzschild"[M_ : M], {t_ : t, r_ : r, theta_ : theta, phi_ : phi}, args___] := 
    MetricTensor[
        DiagonalMatrix[{ - (1 - (2 * M) / r), 1 / (1 - (2 * M) / r), r ^ 2, r ^ 2 * Sin[theta] ^ 2}],
        {t, r, theta, phi},
        args
    ]


(* IsotropicSchwarzschild *)

MetricTensor["IsotropicSchwarzschild"[M_ : M], {t_ : t, x_ : x, y_ : y, z_ : z}, args___] := With[{
    r = Sqrt[x ^ 2 + y ^ 2 + z ^ 2]
},
    MetricTensor[
        DiagonalMatrix[Prepend[ - (1 - M / 2 / r) ^ 2 / (1 + M / 2 / r) ^ 2] @ ConstantArray[(1 + M / 2 / r) ^ 4, 3]],
        {t, x, y, z},
        args
    ]
]


(* EddingtonFinkelstein *)

MetricTensor["EddingtonFinkelstein"[M_ : M], {t_ : t, r_ : r, theta_ : theta, phi_ : phi}, args___] := 
    MetricTensor[
        {
            {- (1 - (2 * M) / r), \[PlusMinus]1, 0, 0},
            {\[PlusMinus]1, 0, 0, 0},
            {0, 0, r ^ 2, 0},
            {0, 0, 0, r ^ 2 * Sin[theta] ^ 2}
        },
        {t, r, theta, phi},
        args
    ]


(* IngoingEddingtonFinkelstein *)

MetricTensor["IngoingEddingtonFinkelstein"[M_ : M], {v_ : v, r_ : r, theta_ : theta, phi_ : phi}, args___] := 
    MetricTensor[
        {
            {- (1 - (2 * M) / r), 1, 0, 0},
            {1, 0, 0, 0},
            {0, 0, r ^ 2, 0},
            {0, 0, 0, r ^ 2 * Sin[theta] ^ 2}
        },
        {v, r, theta, phi},
        args
    ]


(* OutgoingEddingtonFinkelstein *)

MetricTensor["OutgoingEddingtonFinkelstein"[M_ : M], {u_ : u, r_ : r, theta_ : theta, phi_ : phi}, args___] := 
    MetricTensor[
        {
            {- (1 - (2 * M) / r), -1, 0, 0},
            {-1, 0, 0, 0},
            {0, 0, r ^ 2, 0},
            {0, 0, 0, r ^ 2 * Sin[theta] ^ 2}
        },
        {u, r, theta, phi},
        args
    ]


(* GullstrandPainleve *)

MetricTensor["GullstrandPainleve"[M_ : M], {t_ : t, r_ : r, theta_ : theta, phi_ : phi}, args___] := 
    MetricTensor[
        {
            {- (1 - (2 * M) / r), \[PlusMinus]Sqrt[2 * M / r], 0, 0},
            {\[PlusMinus]Sqrt[2 * M / r], 1, 0, 0},
            {0, 0, r ^ 2, 0},
            {0, 0, 0, r ^ 2 * Sin[theta] ^ 2}
        },
        {t, r, theta, phi},
        args
    ]


(* IngoingGullstrandPainleve *)

MetricTensor["IngoingGullstrandPainleve"[M_ : M], {t_ : t, r_ : r, theta_ : theta, phi_ : phi}, args___] := 
    MetricTensor[
        {
            {- (1 - (2 * M) / r), Sqrt[2 * M / r], 0, 0},
            {Sqrt[2 * M / r], 1, 0, 0},
            {0, 0, r ^ 2, 0},
            {0, 0, 0, r ^ 2 * Sin[theta] ^ 2}
        },
        {t, r, theta, phi},
        args
    ]

(* OutgoingGullstrandPainleve *)

MetricTensor["OutgoingGullstrandPainleve"[M_ : M], {t_ : t, r_ : r, theta_ : theta, phi_ : phi}, args___] := 
    MetricTensor[
        {
            {- (1 - (2 * M) / r), - Sqrt[2 * M / r], 0, 0},
            {- Sqrt[2 * M / r], 1, 0, 0},
            {0, 0, r ^ 2, 0},
            {0, 0, 0, r ^ 2 * Sin[theta] ^ 2}
        },
        {t, r, theta, phi},
        args
    ]


(* KruskalSzekeres *)

MetricTensor["KruskalSzekeres"[M_ : M], {T_ : T, X_ : X, theta_ : theta, phi_ : phi}, args___] := With[{
    r = 1 + ProductLog[(X ^ 2 - T ^ 2) / E] 
},
    MetricTensor[
        {
            {- (16 * M ^ 2 * Exp[- r]) / r, 0, 0, 0},
            {0, (16 * M ^ 2 * Exp[-r]) / r, 0, 0},
            {0, 0, 4 M ^ 2 r ^ 2, 0},
            {0, 0, 0, 4 M ^ 2 r ^ 2 * Sin[theta] ^ 2}
        },
        {T, X, theta, phi},
        args
    ]
]


(* Kerr *)

MetricTensor["Kerr"[M_ : M, J_ : J], {t_ : t, r_ : r, theta_ : theta, phi_ : phi}, args___] := With[{
    rho = r ^ 2 + (J * Cos[theta]) ^ 2 / M ^ 2, delta = r ^ 2 - (2 * M * r) + J ^ 2 / M ^ 2
},
    MetricTensor[
        {
            {- 1 + (2 * M * r) / rho, 0, 0, - (2 * r * J * Sin[theta] ^ 2) / rho},
            {0, rho / delta, 0, 0},
            {0, 0, rho, 0},
            {- (2 * r * J * Sin[theta] ^ 2) / rho, 0, 0, 
                (r ^ 2 + J ^ 2 / M ^ 2 + (2 * r * J ^ 2 * Sin[theta] ^ 2) / rho / M) * Sin[theta] ^ 2}
        },
        {t, r, theta, phi},
        args
    ]
]

(* KerrNewman *)

MetricTensor["KerrNewman"[M_ : M, Q_ : Q, J_ : J], {t_ : t, r_ : r, theta_ : theta, phi_ : phi}, args___] := With[{
    rho = r ^ 2 + J ^ 2 / M ^ 2,
    rhoCos = r ^ 2 + (J * Cos[theta]) ^ 2 / M ^ 2,
    delta = r ^ 2 - (2 * M * r) + J ^ 2 / M ^ 2 + Q ^ 2 / (4 Pi)
},
    MetricTensor[
        {
            {(- delta + (J * Sin[theta]) ^ 2 / M ^ 2) / rhoCos, 0, 0, J / M (delta - rho) Sin[theta] ^ 2 / rhoCos},
            {0, rhoCos / delta, 0, 0},
            {0, 0, rhoCos, 0},
            {J / M (delta - rho) Sin[theta] ^ 2 / rhoCos, 0, 0, (rho ^ 2 - J ^ 2 / M ^ 2 delta Sin[theta] ^ 2) Sin[theta] ^ 2 / rhoCos}
        },
        {t, r, theta, phi},
        args
    ]
]


(* ReissnerNordstrom *)

MetricTensor["ReissnerNordstrom"[M_ : M, Q_ : Q], {t_ : t, r_ : r, theta_ : theta, phi_ : phi}, args___] := With[{
    f = 1 - (2 * M) / r + (Q ^ 2) / (4 Pi r ^ 2)
},
    MetricTensor[
        DiagonalMatrix[{- f, 1 / f, r ^ 2, r ^ 2 * Sin[theta] ^ 2}],
        {t, r, theta, phi},
        args
    ]
]


(* Godel *)

MetricTensor["Godel"[omega_ : omega], {t_ : t, x_ : x, y_ : y, z_ : z}, args___] := 
    MetricTensor[
        {
            {- 1 / 2 / omega ^ 2, 0, - Exp[x] / 2 / omega ^ 2, 0},
            {0, 1 / 2 / omega ^ 2, 0, 0},
            {- Exp[x] / 2 / omega ^ 2, 0, - Exp[2 x] / 4 / omega ^ 2, 0},
            {0, 0, 0, 1 / 2 / omega ^ 2}
        },
        {t, x, y, z},
        args
    ]


(* FLRW *)

MetricTensor["FLRW"[k_ : k, a_ : a], {t_ : t, r_ : r, theta_ : theta, phi_ : phi}, args___] := With[{
    at = a[t]
},
    MetricTensor[
        DiagonalMatrix[{- 1, at ^ 2 / (1 - k * r ^ 2), at ^ 2 * r ^ 2, at ^ 2 * r ^ 2 * Sin[theta] ^ 2}],
        {t, r, theta, phi},
        args
    ]
]


(* Mutation *)

MetricTensor[mt_MetricTensor, coordinates_List] := MetricTensor[mt["Matrix"], padCoordiantes[coordinates, mt["Dimension"]], mt["Indices"]]

MetricTensor[mt_MetricTensor, i_ ? BooleanQ] := MetricTensor[mt["Matrix"], mt["Coordinates"], i, mt["Indices"][[2]]]

MetricTensor[mt_MetricTensor, i_ ? BooleanQ, j_ ? BooleanQ] := MetricTensor[mt["Matrix"], mt["Coordinates"], i, j]

MetricTensor[mt_MetricTensor] := mt


(* General constructors *)

MetricTensor[name_String, args___] := MetricTensor[name[], args]

MetricTensor[name : _String[___]] := MetricTensor[name, {}]

MetricTensor[{name_String, params___}, args___] := MetricTensor[name[params], args]

MetricTensor[matrix_ ? SquareMatrixQ] := MetricTensor[matrix, Superscript[x, #] & /@ Range[Length[matrix]]]

MetricTensor[vector_ ? VectorQ] := MetricTensor[DiagonalMatrix[vector]]


MetricTensor[matrix_, coordinates_, i : _ ? BooleanQ : True, j : _ ? BooleanQ : True] := With[{
    st = ShapedTensor[matrix, {i, j}]
},
    MetricTensor[ShapedTensor[st, Shape @@ MapThread[Dimension[#1, #2, coordinates] &, {st["Indices"], {mu, nu}}], coordinates, "g"]]
]

m_MetricTensor /; System`Private`HoldNotValidQ[m] && metricTensorQ[Unevaluated[m]] :=
    System`Private`SetNoEntry[System`Private`HoldSetValid[m]]


(* Properties *)

(m_MetricTensor ? MetricTensorQ)[prop_String | prop_String[args___]] := Prop[m, prop, args]

MetricTensor["Properties"] = {
    "MatrixRepresentation", "ReducedMatrixRepresentation", "Coordinates", "CoordinateOneForms", "Indices", "CovariantQ", 
    "ContravariantQ", "MixedQ", "Symbol", "Dimensions", "SymmetricQ", "DiagonalQ", "Signature", "RiemannianQ", 
    "PseudoRiemannianQ", "LorentzianQ", "RiemannianConditions", "PseudoRiemannianConditions", "LorentzianConditions", 
    "MetricSingularities", "Determinant", "ReducedDeterminant", "Trace", "ReducedTrace", "Eigenvalues", 
    "ReducedEigenvalues", "Eigenvectors", "ReducedEigenvectors", "MetricTensor", "InverseMetricTensor", "LineElement", 
    "ReducedLineElement", "VolumeForm", "ReducedVolumeForm", "TimelikeQ", "LightlikeQ", "SpacelikeQ", 
    "LengthPureFunction", "AnglePureFunction", "Properties"
}

Prop[_, "Properties"] := MetricTensor["Properties"]

Prop[MetricTensor[st_] ? MetricTensorQ, "ShapedTensor"] := st


Prop[mt_, "Matrix"] := mt["Tensor"]

Prop[mt_, "Variables" | "Coordinates"] := mt["Parameters"]

Prop[mt_, "Indices"] := mt["Variance"]


Prop[mt_, prop_String /; StringStartsQ[prop, "Reduced"]] := FullSimplify[mt[StringDelete[prop, "Reduced"]]]

Prop[mt_, "Dimension" | "Dimensions"] := Length[mt["Coordinates"]]

Prop[mt_, "MatrixRepresentation"] :=
    Switch[mt["Indices"],
        {True, True}, mt["Matrix"],
        {False, False}, Inverse[mt["Matrix"]],
        _, IdentityMatrix[mt["Dimension"]]
    ]

Prop[mt_, "CoordinateOneForms"] := DifferentialD /@ mt["Coordinates"]

Prop[mt_, "Signature"] := Block[{
    eigenvalues = Eigenvalues[mt["MatrixRepresentation"]]
},
    {Count[eigenvalues, _ ? Positive], Count[eigenvalues, _ ? Negative], Count[eigenvalues, EqualTo[0]]}
]

Prop[mt_, "FullSignature"] := With[{signature = mt["Signature"]},
    Append[signature, mt["Dimension"] - Total[signature]]
]

Prop[mt_, "SignatureVector"] := Block[{
    p, q, r
},
    {p, q, r} = mt["Signature"];
    Join[
        ConstantArray[1,  p],
        ConstantArray[- 1, q],
        ConstantArray[0, r]
    ]
]

Prop[mt_, "Type"] := Switch[
    mt["Indices"]
    ,
    {True, True},
    "Covariant"
    ,
    {False, False},
    "Contravariant"
    ,
    _,
    "Mixed"
]

Prop[mt_, "CovariantQ"] := mt["Type"] === "Covariant"

Prop[mt_, "ContravariantQ"] := mt["Type"] === "Contravariant"

Prop[mt_, "MixedQ"] := mt["Type"] === "Mixed"

Prop[mt_, "SignatyreType"] := Switch[
    mt["Signature"],
    {0, 0, 0}, "Unknown",
    {p_, 0, p_} | {0, q_, q_}, "Riemannian",
    {p_, q_, 0}, "Pseudo-Riemannian",
    {1, _, 0}, "Lorentzian",
    {_, _, 0}, "Pseudo-Riemannian",
    _, "General"
]

Prop[mt_, "RiemannianQ"] := mt["SignatyreType"] === "Riemannian"

Prop[mt_, "PseudoRiemannianQ"] := mt["SignatyreType"] === "Pseudo-Riemannian"

Prop[mt_, "LorentzianQ"] := mt["SignatyreType"] === "Lorentzian"


Prop[mt_, "Symmetry"] := TensorSymmetry[mt["Tensor"]]

Prop[mt_, "SymmetricQ"] := mt["Symmetry"] === Symmetric[{1, 2}]

Prop[mt_, "DiagonalQ"] := DiagonalMatrixQ[mt["MatrixRepresentation"]]


Prop[mt_, "Inverse" | "InverseMetricTensor"] := MetricTensor[mt, False, False]


Prop[mt_, prop_String, args___] /; MemberQ[ShapedTensor["Properties"], prop] := mt["ShapedTensor"][prop, args]


(* General fallback constructor *)

mt : MetricTensor[arg_, args___] /; ! MetricTensorQ[Unevaluated[mt]] := MetricTensor[MetricTensor[arg], args]


(* Formatting *)

MetricTensor /: MakeBoxes[mt_MetricTensor /; MetricTensorQ[Unevaluated[mt]], TraditionalForm] := With[{
    boxes = ToBoxes[Normal[mt["MatrixRepresentation"]], TraditionalForm]
},
    InterpretationBox[
        boxes,
        mt
    ]
]
    

MetricTensor /: MakeBoxes[mt_MetricTensor /; MetricTensorQ[Unevaluated[mt]], form_] := Block[{
    m = mt["Matrix"], icon
},
    icon = MatrixPlot[
        Map[Replace[{x_ ? (Not @* NumericQ) :> BlockRandom[RandomComplex[], RandomSeeding -> Hash[x]], x_ :> N[x]}], m, {2}],
        ImageSize -> Dynamic[{Automatic, 3.5 * (CurrentValue["FontCapHeight"] / AbsoluteCurrentValue[Magnification])}],
        Frame -> False, FrameTicks -> None
    ];

    BoxForm`ArrangeSummaryBox["MetricTensor", mt, icon,
        {
            {
                BoxForm`SummaryItem[{"Type: ", mt["Type"]}],
                BoxForm`SummaryItem[{"Symbol: ", mt["Symbol"]}]
            },
            {
                BoxForm`SummaryItem[{"Dimensions: ", mt["Dimensions"]}], 
                BoxForm`SummaryItem[{"Coordinates: ", mt["Coordinates"]}]   
            }
        },
        {
            {
                BoxForm`SummaryItem[{"Signature: ", mt["SignatyreType"]}],
                BoxForm`SummaryItem[{"Symmetry: ", mt["Symmetry"]}]
            }
        },
        form,
        "Interpretable" -> Automatic
    ]
]

