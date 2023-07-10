import Lake
open Lake DSL

package Http

@[default_target]
lean_exe http {
  root := `Main
}

@[default_target]
lean_lib Http

require Socket from git
  "https://github.com/xubaiw/lean4-socket.git" @ "main"

require Std from git
  "https://github.com/leanprover/std4/" @ "main"

-- require OpenSSL from git
--   "https://github.com/yatima-inc/OpenSSL.lean" @ "7187dab2f60097194167dbfa5afd862c276f4cd7"
