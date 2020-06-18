{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}

module Main where

import Synquid.Type
import Synquid.Program
import Synquid.Error
import Synquid.Pretty
import Synquid.Parser
import Synquid.Resolver (resolveDecls)
import Synquid.Solver.Monad hiding (name)
import Synquid.Solver.HornClause
import Synquid.Synthesis.Synthesizer
import Synquid.Synthesis.Util
import Synquid.HtmlOutput
import Synquid.Solver.Types

import Control.Monad
import System.Exit
import System.Console.CmdArgs
import System.FilePath
import Data.Char
import Data.Time.Calendar
import Data.Map ((!))
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Control.Lens ((.~), (^.), (%~))

import Data.List.Split

programName = "resyn"
versionName = "0.1"
releaseDate = fromGregorian 2016 8 11

-- | Type-check and synthesize a program, according to command-line arguments
main = do
  res <- cmdArgsRun $ mode
  case res of
    (Synthesis file libs onlyGoals
               appMax scrutineeMax matchMax auxMax fix genPreds explicitMatch unfoldLocals partial incremental consistency symmetry
               lfp bfs
               out_file out_module outFormat resolve
               print_spec print_stats log_ 
               resources mult forall cut nump constTime cegis_max ec res_solver logfile) -> do
                  let 
                    resArgs = defaultResourceArgs {
                    _shouldCheckResources = resources,
                    _checkMultiplicities = mult,
                    _constantTime = constTime,
                    _cegisBound = cegis_max,
                    _enumerate = ec,
                    _rsolver = res_solver,
                    _sygusLog = logfile
                  }
                  let explorerParams = defaultExplorerParams {
                    _eGuessDepth = appMax,
                    _scrutineeDepth = scrutineeMax,
                    _matchDepth = matchMax,
                    _auxDepth = auxMax,
                    _fixStrategy = fix,
                    _predPolyRecursion = genPreds,
                    _abduceScrutinees = not explicitMatch,
                    _unfoldLocals = unfoldLocals,
                    _partialSolution = partial,
                    _incrementalChecking = incremental,
                    _consistencyChecking = consistency,
                    _symmetryReduction = symmetry,
                    _explorerLogLevel = log_,
                    _shouldCut = not cut,
                    _numPrograms = nump,
                    _explorerResourceArgs = resArgs
                  }
                  let solverParams = defaultHornSolverParams {
                    isLeastFixpoint = lfp,
                    optimalValuationsStrategy = if bfs then BFSValuations else MarcoValuations,
                    solverLogLevel = log_
                  }
                  let synquidParams = defaultSynquidParams {
                    goalFilter = liftM (splitOn ",") onlyGoals,
                    outputFormat = outFormat,
                    resolveOnly = resolve,
                    showSpec = print_spec,
                    showStats = print_stats
                  }
                  runOnFile synquidParams explorerParams solverParams file libs

{- Command line arguments -}

deriving instance Typeable FixpointStrategy
deriving instance Data FixpointStrategy
deriving instance Eq FixpointStrategy
deriving instance Show FixpointStrategy

deriving instance Typeable ResourceSolver
deriving instance Data ResourceSolver
deriving instance Eq ResourceSolver

{-# ANN module "HLint: ignore Use camelCase" #-}
{-# ANN module "HLint: ignore Redundant bracket" #-}
{-# ANN module "HLint: ignore" #-}

data CommandLineArgs
    = Synthesis {
        -- | Input
        file :: String,
        libs :: [String],
        only :: Maybe String,
        -- | Explorer params
        app_max :: Int,
        scrutinee_max :: Int,
        match_max :: Int,
        aux_max :: Int,
        fix :: FixpointStrategy,
        generalize_preds :: Bool,
        explicit_match :: Bool,
        unfold_locals :: Bool,
        partial :: Bool,
        incremental :: Bool,
        consistency :: Bool,
        symmetry :: Bool,
        -- | Solver params
        lfp :: Bool,
        bfs_solver :: Bool,
        -- | Output
        out_file :: Maybe String,
        out_module :: Maybe String,
        output :: OutputFormat,
        resolve :: Bool,
        print_spec :: Bool,
        print_stats :: Bool,
        log_ :: Int,
        -- | Resource params
        resources :: Bool,
        multiplicities :: Bool,
        instantiate_foralls :: Bool,
        backtrack :: Bool,
        num_programs :: Int,
        ct :: Bool,
        cegis_max :: Int,
        eac :: Bool,
        res_solver :: ResourceSolver,
        logfile :: Maybe String
      }
  deriving (Data, Typeable, Show, Eq)

synt = Synthesis {
  file                = ""              &= typFile &= argPos 0,
  libs                = []              &= args &= typ "FILES",
  only                = Nothing         &= typ "GOAL,..." &= help ("Only synthesize the specified functions"),
  app_max             = 3               &= help ("Maximum depth of an application term (default: 3)") &= groupname "Explorer parameters",
  scrutinee_max       = 1               &= help ("Maximum depth of a match scrutinee (default: 1)"),
  match_max           = 2               &= help ("Maximum depth of matches (default: 2)") &= name "m",
  aux_max             = 1               &= help ("Maximum depth of auxiliary functions (default: 1)") &= name "x",
  fix                 = FirstArgument   &= help (unwords ["What should termination metric for fixpoints be derived from?", show AllArguments, show FirstArgument, show DisableFixpoint, show Nonterminating, "(default:", show FirstArgument, ")"]),
  generalize_preds    = True            &= help ("Make recursion polymorphic in abstract refinements (default: False)"),
  explicit_match      = False           &= help ("Do not abduce match scrutinees (default: False)") &= name "e",
  unfold_locals       = False           &= help ("Use all variables, as opposed to top-level function arguments only, in match scrutinee abduction (default: False)"),
  partial             = False           &= help ("Generate best-effort partial solutions (default: False)") &= name "p",
  incremental         = True            &= help ("Subtyping checks during bottom-up phase (default: True)"),
  consistency         = True            &= help ("Check incomplete application types for consistency (default: True)"),
  symmetry            = False           &= help ("Use symmetry reductions (default: False)") &= name "s",
  lfp                 = False           &= help ("Use least fixpoint solver (only works for type checking, default: False)") &= groupname "Solver parameters",
  bfs_solver          = False           &= help ("Use BFS instead of MARCO to solve second-order constraints (default: False)"),
  resolve             = False           &= help ("Resolve only; no type checking or synthesis (default: False)"),
  out_file            = Nothing         &= help ("Generate Haskell output file (default: none)") &= typFile &= name "o" &= opt "" &= groupname "Output",
  out_module          = Nothing         &= help ("Name of Haskell module to generate (default: from file name)") &= typ "Name",
  output              = defaultFormat   &= help ("Output format: Plain, Ansi or Html (default: " ++ show defaultFormat ++ ")") &= typ "FORMAT",
  print_spec          = True            &= help ("Show specification of each synthesis goal (default: True)"),
  print_stats         = False           &= help ("Show specification and solution size (default: False)"),
  log_                = 0               &= help ("Logger verboseness level (default: 0)") &= name "l",
  resources           = True            &= help ("Verify resource usage (default: True)") &= name "r" &= groupname "Resource analysis parameters",
  multiplicities      = True            &= help ("Use multiplicities when verifying resource usage (default: True)"),
  instantiate_foralls = True            &= help ("Solve exists-forall constraints by instantiating universally quantified expressions (default: True)"),
  backtrack           = False           &= help ("Backtrack past successfully synthesized branches (default: False)") &= name "b",
  num_programs        = 1               &= help ("Number of programs to produce if possible (default: 1)"),
  ct                  = False           &= help ("Require that all branching expressions consume a constant amount of resources (default: False)"),
  cegis_max           = 100             &= help ("Maximum number of iterations through the CEGIS loop (default: 100)"),
  eac                 = False           &= help ("Enumerate-and-check instead of round-trip resource analysis (default: False)"),
  res_solver          = Incremental     &= help (unwords ["Which solver should be used for resource constraints?", show CVC4, show CEGIS, show Incremental, "(default: ", show Incremental, ")"]),
  logfile             = Nothing         &= help ("File for logging SYGUS constraints (default: no logging)")
  } &= auto &= help "Synthesize goals specified in the input file"
    where
      defaultFormat = outputFormat defaultSynquidParams


mode = cmdArgsMode $ synt &=
  help "Synquid program synthesizer" &=
  program programName &=
  summary (programName ++ " v" ++ versionName ++ ", " ++ showGregorian releaseDate)

-- | Parameters for template exploration
defaultExplorerParams = ExplorerParams {
  _eGuessDepth = 3,
  _scrutineeDepth = 1,
  _matchDepth = 2,
  _auxDepth = 1,
  _fixStrategy = AllArguments,
  _polyRecursion = True,
  _predPolyRecursion = False,
  _abduceScrutinees = True,
  _unfoldLocals = False,
  _partialSolution = False,
  _incrementalChecking = True,
  _consistencyChecking = False,
  _splitMeasures = True,
  _symmetryReduction = False,
  _context = id,
  _sourcePos = noPos,
  _explorerLogLevel = 0,
  _shouldCut = True,
  _numPrograms = 1,
  _explorerResourceArgs = defaultResourceArgs
}

defaultResourceArgs = ResourceArgs {
  _shouldCheckResources = True,
  _checkMultiplicities = True,
  _constantTime = False,
  _cegisBound = 100,
  _enumerate = False,
  _rsolver = Incremental,
  _sygusLog = Nothing
}

-- | Parameters for constraint solving
defaultHornSolverParams = HornSolverParams {
  pruneQuals = True,
  isLeastFixpoint = False,
  optimalValuationsStrategy = MarcoValuations,
  semanticPrune = True,
  agressivePrune = True,
  candidatePickStrategy = InitializedWeakCandidate,
  constraintPickStrategy = SmallSpaceConstraint,
  solverLogLevel = 0
}

-- | Output format
data OutputFormat = Plain -- ^ Plain text
  | Ansi -- ^ Text with ANSI-terminal special characters
  | Html -- ^ HTML
  deriving (Typeable, Data, Eq, Show)

-- | 'printDoc' @format doc@ : print @doc@ to the console using @format@
printDoc :: OutputFormat -> Doc -> IO()
printDoc Plain doc = putDoc (plain doc) >> putStr "\n"
printDoc Ansi doc = putDoc doc >> putStr "\n"
printDoc Html doc = putStr (showDocHtml (renderPretty 0.4 100 doc))

-- | Parameters of the synthesis
data SynquidParams = SynquidParams {
  goalFilter :: Maybe [String],
  outputFormat :: OutputFormat,                -- ^ Output format
  resolveOnly :: Bool,                         -- ^ Stop after resolution step
  verifyOnly :: Bool,
  showSpec :: Bool,                            -- ^ Print specification for every synthesis goal
  showStats :: Bool                            -- ^ Print specification and solution size
}

defaultSynquidParams = SynquidParams {
  goalFilter = Nothing,
  outputFormat = Plain,
  resolveOnly = False,
  verifyOnly = False,
  showSpec = True,
  showStats = False
}


data SynthesisResult = SynthesisResult {
  prog :: RProgram,
  finalTState :: TypingState,
  extraResults :: [(RProgram, TypingState)],
  goal :: Goal
} deriving (Eq, Ord)

-- | Parse and resolve file, then synthesize the specified goals
runOnFile :: SynquidParams -> ExplorerParams -> HornSolverParams 
                           -> String -> [String] -> IO ()
runOnFile synquidParams explorerParams solverParams file libs = do
  declsByFile <- parseFromFiles (libs ++ [file])
  let decls = concat $ map snd declsByFile
  case resolveDecls decls of
    Left resolutionError -> (pdoc $ pretty resolutionError) >> pdoc empty >> exitFailure
    Right (goals, cquals, tquals) -> when (not $ resolveOnly synquidParams) $ do
      results <- mapM (synthesizeGoal cquals tquals) (requested goals)
      when (not (null results) && showStats synquidParams) $ printStats results declsByFile
      return ()

  where
    parseFromFiles [] = return []
    parseFromFiles (file:rest) = do
      parseResult <- parseFromFile parseProgram file
      case parseResult of
        Left parseErr -> (pdoc $ pretty $ toErrorMessage parseErr) >> pdoc empty >> exitFailure
        -- Right ast -> print $ vsep $ map pretty ast
        Right decls -> let decls' = if null rest then decls else filter (not . isSynthesisGoal) decls in -- Remove implementations from libraries
          ((file, decls') :) <$> parseFromFiles rest
    requested goals = case goalFilter synquidParams of
      Just filt -> filter (\goal -> gName goal `elem` filt) goals
      _ -> goals
    pdoc = printDoc (outputFormat synquidParams)
    synthesizeGoal cquals tquals goal = do
      when ((gSynthesize goal) && (showSpec synquidParams)) $ pdoc (prettySpec goal)
      -- print empty
      -- print $ vMapDoc pretty pretty (allSymbols $ gEnvironment goal)
      -- print $ pretty (gSpec goal)
      -- print $ vMapDoc pretty pretty (_measures $ gEnvironment goal)
      mProg <- synthesize (updateExplorerParams explorerParams goal) (updateSolverParams solverParams goal) goal cquals tquals
      case mProg of
        Left typeErr -> pdoc (pretty typeErr) >> pdoc empty >> exitFailure
        Right progs  -> do
          -- Print synthesized program
          when (gSynthesize goal) $ mapM_ (\p -> pdoc (prettySolution goal (fst p)) >> pdoc empty) progs
          let result = assembleResult goal progs
          return result
    assembleResult goal ps = SynthesisResult (fst (head ps)) (snd (head ps)) (tail ps) goal
    updateLogLevel goal orig = if gSynthesize goal then orig else 0 -- prevent logging while type checking measures

    updateExplorerParams eParams goal =
      let eParams' = explorerLogLevel %~ updateLogLevel goal $ eParams
      in explorerResourceArgs . shouldCheckResources .~ ((gSynthesize goal) && (eParams ^. (explorerResourceArgs . shouldCheckResources))) $ eParams'

    updateSolverParams sParams goal = sParams { solverLogLevel = (updateLogLevel goal (solverLogLevel sParams))}

    printStats results declsByFile = do
      let env = gEnvironment $ goal (head results)
      let measureCount = Map.size $ env^.measureDefs
      let numC = sum $ map (length . _resourceConstraints . finalTState) results
      let specSize = sum $ map (typeNodeCount . toMonotype . unresolvedSpec . goal) results
      let solutionSize = sum $ map (programNodeCount . prog) results
      pdoc $ vsep $ [
                parens (text "Goals:" <+> pretty (length results)),
                parens (text "Measures:" <+> pretty measureCount),
                parens (text "Spec size:" <+> pretty specSize),
                parens (text "Solution size:" <+> pretty solutionSize),
                parens (text "Number of resource constraints:" <+> pretty numC),
                empty]

