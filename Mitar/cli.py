import sys, argparse
from Mitar.make import make
from Mitar.clean import clean

def Mitar_make(args: argparse.Namespace, ):
    make(args.input_file)
    if not args.keep:
        clean(False)

def Mitar_clean(args: argparse.Namespace):
    clean(True)

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
    parser_make.add_argument("input_file")
    parser_make.add_argument(
        "-k", "--keep",
        action = "store_true",
        help = "Keep Lean2TeX's auxiliary files"
    )
    parser_make.set_defaults(func = Mitar_make)

    parser_clean = subparsers.add_parser("clean")
    parser_clean.set_defaults(func = Mitar_clean)

    commands = subparsers.choices.keys()
    if len(sys.argv) > 1 and sys.argv[1] not in commands and not sys.argv[1].startswith('-'):
        sys.argv.insert(1, 'make')

    args = parser.parse_args()
    args.func(args)
