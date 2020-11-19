""" Entry point for using Input/Output automaton frontend"""

import argparse
import asyncio
import configparser
import sys
import time

from dione.frontend.translator_dafny import TranslatorDafny
from dione.verification_engine.prover_dafny import ProverDafny


async def run(options):
    # FIXME Is it possible to spin up dafny-server subprocess and
    #  translate IOA code concurrently?
    dfy_exe = options.dafny_server
    dfy_code = TranslatorDafny(options.ioa).get_dafny_code()
    print("Translating Dafny Code:")
    time.sleep(2.0)
    print(dfy_code)
    print("Verifying Dafny Code:")
    async with ProverDafny(dfy_exe) as prover:  # This creates a new process
        # TODO Specify pattern to prove invariant proof only
        print(await prover.verify(dfy_code, ["-proc:*proof_q*"]))


def main(args=None):
    if args is None:
        # main function shouldn't take arguments if using setuptools.
        # Hence, we read arguments from sys.argv
        args = sys.argv[1:]

    options = parse_options(args)

    if sys.platform == 'win32':
        asyncio.set_event_loop_policy(asyncio.WindowsProactorEventLoopPolicy())

    asyncio.run(run(options))


def parse_options(args):
    """ Parse both config file and commandline arguments where the command line
        values overrides the ones in config file.
        Inspired by https://stackoverflow.com/questions/3609852/
    """
    # Parse any conf_file specification
    # We make this parser with add_help=False so that
    # it doesn't parse -h and print help.
    conf_parser = argparse.ArgumentParser(
        description=__doc__,  # printed with -h/--help
        # Don't mess with format of description
        formatter_class=argparse.RawDescriptionHelpFormatter,
        # Turn off help, so we print all options in response to -h
        add_help=False
        )
    conf_parser.add_argument("-c", "--conf",
                             type=argparse.FileType('r'),
                             help="Specify config file",
                             default="setup.cfg"
                             )
    args, remaining_argv = conf_parser.parse_known_args()

    config = configparser.ConfigParser()
    assert args.conf
    config.read_file(args.conf)

    defaults = {'dafny_server': ""}
    defaults.update(dict(config.items("dione")))  # FIXME use package name

    # Parse rest of arguments
    # Don't suppress add_help here so it will handle -h
    parser = argparse.ArgumentParser(
        prog="dione",  # FIXME use package name
        description='Verification/Simulation for Input/Output Automaton',
        parents=[conf_parser]  # Inherit options from config_parser
        )
    parser.set_defaults(**defaults)
    parser.add_argument('ioa', type=argparse.FileType('r'), help='Input IOA file')

    def __check_file(p: str):
        from pathlib import Path
        f = Path(p).expanduser()
        if not f.is_file():
            raise argparse.ArgumentTypeError(
                "Path \"" + p + "\" specified by " + args.conf.name + " or cmdline is not a file")
        return str(f.resolve())
    parser.add_argument(
        "--dafny_server",
        help="Specify executable dafny-server or DafnyServer.exe",
        type=__check_file
    )

    return parser.parse_args(remaining_argv)


if __name__ == "__main__":
    main()
