import os
import shutil
from pathlib import Path
from invoke import run, task

from mathlibtools.lib import LeanProject

from blueprint.tasks import web, bp, serve

ROOT = Path(__file__).parent

@task
def decls(ctx):
    proj = LeanProject.from_path(ROOT)
    proj.pickle_decls(ROOT/'decls.pickle')

@task(decls, bp, web)
def all(ctx):
    shutil.copy2(ROOT/'blueprint'/'print'/'print.pdf', ROOT/'blueprint'/'web'/'blueprint.pdf')

@task(serve)
def dev(ctx):
    pass