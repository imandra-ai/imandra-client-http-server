open Lwt
open Cohttp
open Cohttp_lwt_unix
module L = Imandra_client_lib
module LI = Imandra_client_lib.Imandra
module D = Api.Decoders (Decoders_yojson.Basic.Decode)
module E = Api.Encoders (Decoders_yojson.Basic.Encode)

let logic_eval_result ~(src_syntax : Api.src_syntax) src =
  let open Api in
  let syntax =
    match src_syntax with
    | Reason ->
        Imandra_syntax.Syntax.Reason
    | Iml ->
        Imandra_syntax.Syntax.Iml
  in
  (* Note, if the string contains #program;; this can still run program mode stuff *)
  Imandra_util.Pconfig.(
    with_mode_assigned ~to_:State.Logic (fun () ->
        Imandra_syntax.Syntax.with_local syntax (fun () ->
            LI.eval_string_result ~quiet:true src)))


let print_instance (printer_details : Api.Request.printer_details) =
  let Api.Request.{ name; cx_var_name } = printer_details in
  Imandra_util.Pconfig.(
    with_mode_assigned ~to_:State.Program (fun () ->
        Imandra_syntax.Syntax.with_local Imandra_syntax.Syntax.Iml (fun () ->
            LI.eval_string_returning_string
              (Printf.sprintf "%s CX.%s" name cx_var_name))))


let spec = Spec.spec

let transform_verify_result
    ~(printer_details : Api.Request.printer_details option) r =
  let open L.Verify in
  let mapped =
    match r with
    | V_proved _ ->
        Api.Response.V_proved
    | V_proved_upto { upto; _ } ->
        Api.Response.V_proved_upto
          ( match upto with
          | L.Event.Upto_steps s ->
              Api.Response.Upto_steps s
          | L.Event.Upto_bound b ->
              Api.Response.Upto_bound b )
    | V_refuted { model_str; _ } ->
        Api.Response.V_refuted
          Api.Response.
            { instance =
                { model =
                    { syntax = Api.Iml
                    ; src_base64 = Base64.encode_string model_str
                    }
                ; type_ = "counterexample"
                ; printed =
                    printer_details
                    |> CCOpt.map (fun pd -> print_instance pd)
                }
            }
    | V_unknown { reason; _ } ->
        Api.Response.V_unknown Api.Response.{ unknown_reason = reason }
  in
  mapped |> E.Response.verify_result


let transform_instance_result
    ~(printer_details : Api.Request.printer_details option) r =
  let open L.Instance in
  let mapped =
    match r with
    | I_unsat _ ->
        Api.Response.I_unsat
    | I_unsat_upto { upto; _ } ->
        Api.Response.I_unsat_upto
          ( match upto with
          | L.Event.Upto_steps s ->
              Api.Response.Upto_steps s
          | L.Event.Upto_bound b ->
              Api.Response.Upto_bound b )
    | I_sat { model_str; _ } ->
        Api.Response.I_sat
          Api.Response.
            { instance =
                { model =
                    { syntax = Api.Iml
                    ; src_base64 = Base64.encode_string model_str
                    }
                ; type_ = "instance"
                ; printed =
                    printer_details
                    |> CCOpt.map (fun pd -> print_instance pd)
                }
            }
    | I_unknown { reason; _ } ->
        Api.Response.I_unknown Api.Response.{ unknown_reason = reason }
  in
  mapped |> E.Response.instance_result


let pp_exn fmt e =
  match e with
  | Typetexp.Error (_, env, e) ->
      CCFormat.fprintf fmt "%a" (Typetexp.report_error env) e
  | Typecore.Error (_, env, e) ->
      CCFormat.fprintf fmt "%a" (Typecore.report_error env) e
  | _ ->
      let s = Printexc.to_string e in
      CCFormat.fprintf fmt "%s" s


let bad_request (error_msg : string) =
  let open Api.Response in
  let body =
    { error = error_msg }
    |> Decoders_yojson.Basic.Encode.encode_string E.Response.error_response
  in
  Server.respond_string ~status:`Bad_request ~body ()


let with_decoded_json decoder json_str f =
  let parsed =
    Decoders_yojson.Basic.Decode.decode_string decoder json_str
    |> CCResult.map_err (fun e ->
           bad_request
             (CCFormat.asprintf "%a" Decoders_yojson.Basic.Decode.pp_error e))
  in
  match parsed |> CCResult.map f with Ok r -> r | Error r -> r


let error_response e =
  let body =
    let open Api.Response in
    let s = CCFormat.asprintf "%a" pp_exn e in
    { error = s }
    |> Decoders_yojson.Basic.Encode.encode_string E.Response.error_response
  in
  Server.respond_string ~status:`Unprocessable_entity ~body ()


let ok_response json =
  Server.respond_string ~status:`OK ~body:(Yojson.Basic.to_string json) ()


let map_induct = function
  | Api.Request.Hints.Induct.Default ->
      Imandra_surface.Hints.Induct.Default
  | Api.Request.Hints.Induct.(Functional { f_name }) ->
      let db = Imandra_surface.Event.State.get Imandra_interactive.Globals_.event_state_ in
      let f_name = Some (Imandra_surface.Event.DB.fun_id_of_str db f_name) in
      Imandra_surface.Hints.Induct.(Functional { f_name })
  | Api.Request.Hints.Induct.(Structural { vars; style }) ->
      Imandra_surface.Hints.Induct.(Structural { vars; style })


let map_hint (h : Api.Request.Hints.t) =
  let open Api.Request.Hints in
  Imandra_surface.Hints.(
    make
      ( match h.method_ with
      | Api.Request.Hints.Method.(Unroll { steps }) ->
          Imandra_surface.Hints.Method.(Unroll { steps })
      | Api.Request.Hints.Method.(Ext_solver { name }) ->
          Imandra_surface.Hints.Method.(Ext_solver { name })
      | Api.Request.Hints.Method.Auto ->
          Imandra_surface.Hints.Method.Auto
      | Api.Request.Hints.Method.(Induct i) ->
          Imandra_surface.Hints.Method.Induct (map_induct i) ))


let handle method_ path body =
  let open Api.Request in
  match (method_, path) with
  | `GET, "/status" ->
      Server.respond_string ~status:`OK ~body:"OK" ()
  | `GET, "/spec" ->
      let headers =
        Header.of_list [ ("content-type", "application/x-yaml") ]
      in
      Server.respond_string ~headers ~status:`OK ~body:spec ()
  | `POST, "/shutdown" ->
      Lwt.async (fun () ->
          let open Lwt.Infix in
          print_endline "Shutting down..." ;
          Lwt_unix.sleep 0.1 >>= fun () -> exit 0) ;

      Server.respond_string ~status:`OK ~body:"OK" ()
  | `POST, "/eval/by-src" ->
      with_decoded_json D.Request.eval_req_src body (fun req_src ->
          let src = Base64.decode_exn req_src.src_base64 in
          let to_eval = Printf.sprintf "%s" src in
          match logic_eval_result ~src_syntax:req_src.syntax to_eval () with
          | Ok _ ->
              (* We throw the top result list away here as it's empty unless top
             result is turned on, and we have it turned off for efficiency. Better to
             force the user to use a defined function call endpoint, e.g. /verify
             rather than having to deal with the more arbitrary output *)
              ok_response (`Assoc [ ("success", `Bool true) ])
          | Error e ->
              error_response e)
  | `POST, "/verify/by-src" ->
      with_decoded_json D.Request.verify_req_src body (fun req_src ->
          let src = Base64.decode_exn req_src.src_base64 in
          let s = Imandra_util.Util.gensym () in
          let to_eval = Printf.sprintf "let %s = %s" s src in
          match logic_eval_result ~src_syntax:req_src.syntax to_eval () with
          | Error e ->
              error_response e
          | Ok _ ->
            ( try
                let hints = req_src.hints |> CCOpt.map (fun h -> map_hint h) in
                L.Verify.top ~reflect:true ~quiet:true ?hints s
                |> transform_verify_result
                     ~printer_details:req_src.instance_printer
                |> ok_response
              with
            | e ->
                error_response e ))
  | `POST, "/verify/by-name" ->
      with_decoded_json D.Request.verify_req_name body (fun req_name ->
          try
            let hints = req_name.hints |> CCOpt.map (fun h -> map_hint h) in
            L.Verify.top ~reflect:true ~quiet:true ?hints req_name.name
            |> transform_verify_result
                 ~printer_details:req_name.instance_printer
            |> ok_response
          with
          | e ->
              error_response e)
  | `POST, "/instance/by-src" ->
      with_decoded_json D.Request.instance_req_src body (fun req_src ->
          let src = Base64.decode_exn req_src.src_base64 in
          let s = Imandra_util.Util.gensym () in
          let to_eval = Printf.sprintf "let %s = %s" s src in
          let hints = req_src.hints |> CCOpt.map (fun h -> map_hint h) in
          match logic_eval_result ~src_syntax:req_src.syntax to_eval () with
          | Error e ->
              error_response e
          | Ok _ ->
            ( try
                L.Instance.top ~reflect:true ~quiet:true ?hints s
                |> transform_instance_result
                     ~printer_details:req_src.instance_printer
                |> ok_response
              with
            | e ->
                error_response e ))
  | `POST, "/instance/by-name" ->
      with_decoded_json D.Request.instance_req_name body (fun req_name ->
          try
            let hints = req_name.hints |> CCOpt.map (fun h -> map_hint h) in
            let json =
              L.Instance.top ~reflect:true ~quiet:true ?hints req_name.name
              |> transform_instance_result
                   ~printer_details:req_name.instance_printer
            in
            ok_response json
          with
          | e ->
              error_response e)
  | `POST, "/reset" ->
      L.System.reset () ;
      ok_response (`Assoc [])
  | _ ->
      Server.respond_string ~status:`Not_found ~body:"Not found" ()


let default_port = 3000

let server_name = ref "imandra_server"

let reason = ref false

let req = ref []

let port = ref default_port

let dirs = ref []

let lock = ref ~-1

let use_tcp = ref false

let address = ref None

let speclist =
  Arg.align
    [ ( "-server"
      , Arg.Set_string server_name
      , " Binary to use as imandra server, defaults to imandra_server" )
    ; ("-reason", Arg.Set reason, " enable reason syntax")
    ; ( "-require"
      , Arg.String (fun s -> req := s :: !req)
      , " Require given library" )
    ; ( "-timeout"
      , Arg.Int Imandra_util.Pconfig.State.Set.timeout
      , " Timeout (in ms) for the solver" )
    ; ( "-port"
      , Arg.Set_int port
      , Printf.sprintf " port to listen on (default %d)" default_port )
    ; ( "-dir"
      , Arg.String (fun s -> dirs := s :: !dirs)
      , " add directory to load path" )
    ; ("-lockdown", Arg.Set_int lock, " lockdown mode to the given user id")
    ; ("-address", Arg.String (fun s -> address := Some(s)), " Socket address used to communicate with the server")
    ; ("-tcp", Arg.Set use_tcp, " Use tcp to communicate with server")
    ]


let http_server (port : int) =
  let callback _conn req body =
    let uri = req |> Request.uri in
    let path = uri |> Uri.path in
    let _meth = req |> Request.meth in
    let _headers = req |> Request.headers |> Header.to_string in
    body
    |> Cohttp_lwt.Body.to_string
    >>= fun body_str ->
    let res =
      try handle _meth path body_str with
      | e ->
          Server.respond_string
            ~status:`Internal_server_error
            ~body:(Printexc.to_string e)
            ()
    in
    res
    |> Lwt.map (fun ((res, body) : Cohttp.Response.t * _) ->
           ( Cohttp.Response.make
               ~status:res.Response.status
               ~headers:
                 (Cohttp.Header.add
                    res.Response.headers
                    "Access-Control-Allow-Origin"
                    "*")
               ()
           , body ))
  in
  print_endline (Printf.sprintf "Server starting on port %d..." port) ;
  flush_all () ;
  Server.create ~mode:(`TCP (`Port port)) (Server.make ~callback ())


let () =
  Arg.parse
    speclist
    print_endline
    "Query Imandra via HTTP.\n\n\
     curl localhost:<port>/spec for an open api 3.0 spec of available \
     endpoints and their parameters.\n" ;
  if !lock >= 0 then LI.set_lockdown !lock ;
  List.iter LI.require_lib_at_init (List.rev !req) ;
  let syntax =
    if !reason then Imandra_syntax.Syntax.Reason else Imandra_syntax.Syntax.Iml
  in
  Imandra_syntax.Syntax.set syntax ;
  Imandra_util.Pconfig.State.Set.print_banner false ;
  List.iter Imandra_interactive.Pconfig_io.add_to_load_path !dirs ;
  Imandra_client_lib.Client.with_server ~server_name:!server_name
    ?address:!address
    ~use_tcp:!use_tcp
    (fun () ->
      LI.do_init ~linenoise:false ~syntax () ;
      Lwt_main.run (http_server !port))
