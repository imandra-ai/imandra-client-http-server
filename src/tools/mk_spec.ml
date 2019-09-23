let () =
  let yaml = Sys.argv.(1) in
  let content = CCIO.with_in yaml CCIO.read_all in
  Printf.printf "let spec = {specgen|\n\
                 %s\n\
                 |specgen}\n" content;
  flush stdout
