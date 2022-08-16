import os
from pathlib import Path
import http.server
import socketserver

from invoke import run, task

BP_DIR = Path(__file__).parent

@task
def bp(ctx):
    cwd = os.getcwd()
    os.chdir(BP_DIR)
    # run('mkdir -p print && cd src && xelatex -output-directory=../print print.tex')
    # run('cd print && bibtex print.aux', env={'BIBINPUTS': '../src'})
    # run('cd src && xelatex -output-directory=../print print.tex')
    # run('cd src && xelatex -output-directory=../print print.tex')
    run('mkdir -p print && cd src && tectonic --keep-intermediates --outdir ../print print.tex')
    run('cp print/print.bbl src/web.bbl')
    os.chdir(cwd)

@task
def web(ctx):
    cwd = os.getcwd()
    os.chdir(BP_DIR/'src')
    run('plastex -c plastex.cfg web.tex', env={'TEXINPUTS': '../src'})
    os.chdir(cwd)

@task
def serve(ctx):
    port = 8080
    cwd = os.getcwd()
    os.chdir(BP_DIR/'web')
    Handler = http.server.SimpleHTTPRequestHandler
    print(f'http://localhost:{port}/')
    httpd = socketserver.TCPServer(('', port), Handler)
    httpd.serve_forever()
    os.chdir(cwd)