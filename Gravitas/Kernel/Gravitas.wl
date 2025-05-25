BeginPackage["WolframInstitute`Gravitas`"]

$SubPackages = {"ADMDecomposition", 
  "ADMStressEnergyDecomposition", "AngularMomentumDensityTensor", 
  "AngularMomentumTensor", "BachTensor", "ChristoffelSymbols", 
  "DiscreteHypersurfaceDecomposition", "DiscreteHypersurfaceGeodesic", 
  "EinsteinTensor", "ElectrograviticTensor", "ElectromagneticTensor", 
  "MetricTensor", "RicciTensor", "RiemannTensor", "SchoutenTensor", 
  "SolveADMEquations", "SolveEinsteinEquations", 
  "SolveElectrovacuumEinsteinEquations", "SolveVacuumADMEquations", 
  "StressEnergyTensor", "WeylTensor"
}

Scan[
    Get[$Context <> # <> "`"] &,
    $SubPackages
]

EndPackage[]
