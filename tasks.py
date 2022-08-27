import os
import shutil
from pathlib import Path
from invoke import run, task

from mathlibtools.lib import LeanProject
import http.server
import socketserver

# from blueprint.tasks import web, bp, serve, dev

ROOT = Path(__file__).parent
BP_DIR = ROOT/'blueprint'

@task
def decls(ctx):
    """
    Collect Lean declarations from Lean sources for referencing in the blueprint
    """

    proj = LeanProject.from_path(ROOT)
    proj.pickle_decls(ROOT/'decls.pickle')

@task
def bp(ctx):
    """
    Build the blueprint PDF file and prepare src/web.bbl for task `web`
    """

    cwd = os.getcwd()
    os.chdir(BP_DIR)
    run('mkdir -p print && cd src && tectonic --keep-intermediates --outdir ../print print.tex')
    run('cp print/print.bbl src/web.bbl')
    os.chdir(cwd)

@task
def web(ctx):
    """
    Build the blueprint website
    """

    cwd = os.getcwd()
    os.chdir(BP_DIR/'src')
    run('plastex -c plastex.cfg web.tex')
    os.chdir(cwd)

@task
def serve(ctx, port=8080):
    """
    Serve the blueprint website assuming the blueprint website is already built
    """

    class MyTCPServer(socketserver.TCPServer):
        def server_bind(self):
            import socket
            self.socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            self.socket.bind(self.server_address)

    cwd = os.getcwd()
    os.chdir(BP_DIR/'web')

    Handler = http.server.SimpleHTTPRequestHandler
    httpd = MyTCPServer(('', port), Handler)

    try:
        (ip, port) = httpd.server_address
        ip = ip or 'localhost'
        print(f'Serving http://{ip}:{port}/ ...')
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    httpd.server_close()

    os.chdir(cwd)

@task
def dev(ctx):
    """
    Serve the blueprint website, rebuild PDF and the website on file changes
    """

    from watchfiles import run_process, DefaultFilter

    def callback(changes):
        print('Changes detected:', changes)
        bp(ctx)
        web(ctx)
    
    run_process(BP_DIR/'src', target='inv serve', callback=callback,
        watch_filter=DefaultFilter(
            ignore_entity_patterns=(
                '.*\.aux$',
                '.*\.log$',
                '.*\.fls$',
                '.*\.fdb_latexmk$',
                '.*\.bbl$',
                '.*\.paux$',
                '.*\.pdf$',
                '.*\.out$',
                '.*\.blg$',
                '.*\.synctex.*$',
            )
        ))

@task(decls, bp, web)
def all(ctx):
    """
    Run all tasks: `decls`, `bp`, and `web`
    """
    
    shutil.copy2(BP_DIR/'print'/'print.pdf', BP_DIR/'web'/'blueprint.pdf')