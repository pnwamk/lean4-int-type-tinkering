import Lake
open Lake DSL

package «int-type-tinkering» where
  -- add package configuration options here

lean_lib «IntTypeTinkering» where
  -- add library configuration options here

@[default_target]
lean_exe «int-type-tinkering» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]
  require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.0.1"
