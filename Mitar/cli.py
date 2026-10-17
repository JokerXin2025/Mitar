import sys, argparse
from Mitar.make import make
from Mitar.clean import clean
from Mitar.tactic import tactic_register_dir
from Mitar.strategy import load_strategy_configs, register_strategies
from Mitar.project import MitarError
from Mitar.serve import serve
from pathlib import Path


def Mitar_make(args: argparse.Namespace):
    # Load additional Tactic/Strategy directories from each config root.
    for d in args.config:
        p = Path(d)
        if p.is_dir():
            if (p / "Tactic").is_dir():
                tactic_register_dir((p / "Tactic").resolve())
            strategy_configs = load_strategy_configs(p / "Strategy") if (p / "Strategy").is_dir() else {}
            register_strategies(strategy_configs)
    make(args.target, args.cache, args.language)


def Mitar_clean(args: argparse.Namespace):
    clean(True)


def Mitar_serve(args: argparse.Namespace):
    host = "0.0.0.0" if args.lan else args.host
    serve(Path(args.target), host, args.port, args.cert, args.key)


def main():

    parser = argparse.ArgumentParser(
        prog = "mitar",
        description = "An automatic informalization tool for mathematical proofs in Lean4"
    )

    subparsers = parser.add_subparsers(
        title = "commands",
        dest = "command",
        required = True
    )

    parser_make = subparsers.add_parser("make")
    parser_make.add_argument("target", help = "Lean project directory or module name")
    parser_make.add_argument(
        "-c", "--cache",
        action = "store_true",
        help = "Render existing ProofScript output without compiling Lean"
    )
    parser_make.add_argument(
        "-C", "--config",
        action = "append",
        default = [],
        help = (
            "Additional config root to load (may be repeated). "
            "Tactic/ and Strategy/ subdirectories are scanned."
        )
    )
    parser_make.add_argument(
        "--language",
        choices=("zh", "en"),
        default=None,
        help="Default theorem-proof language; both languages remain available in the page.",
    )
    parser_make.set_defaults(func = Mitar_make)

    parser_clean = subparsers.add_parser("clean")
    parser_clean.set_defaults(func = Mitar_clean)

    parser_serve = subparsers.add_parser("serve", help="Serve .Mitar/build with Wasm headers")
    parser_serve.add_argument("target", nargs="?", default=".", help="Lean project directory")
    parser_serve.add_argument("--host", default="127.0.0.1", help="Bind address")
    parser_serve.add_argument("--port", type=int, default=8000, help="Bind port")
    parser_serve.add_argument("--lan", action="store_true", help="Listen on all network interfaces")
    parser_serve.add_argument("--cert", type=Path, help="TLS certificate for HTTPS")
    parser_serve.add_argument("--key", type=Path, help="TLS private key for HTTPS")
    parser_serve.set_defaults(func=Mitar_serve)

    commands = subparsers.choices.keys()
    if len(sys.argv) > 1 and sys.argv[1] not in commands and not sys.argv[1].startswith('-'):
        sys.argv.insert(1, 'make')

    args = parser.parse_args()
    try:
        args.func(args)
    except MitarError as error:
        parser.exit(1, f"mitar: error: {error}\n")


if __name__ == "__main__":
    main()
