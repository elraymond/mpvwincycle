#!/usr/bin/python3 -u

import sys
import os
import signal
import daemon
import traceback
import socket
import select
import re
import time
import ewmh
from Xlib import X
from time import sleep
from itertools import chain
from pprint import pformat


###
### variables to be modified by user if he/she likes to
###

# default number of workspace/desktop this script should exclusively operate on;
# set to None to always operate on current desktop
#mpv_desktop = 0 # manage mpv windows on desktop number 0 exclusively
mpv_desktop = None # always manage mpv windows on the desktop that is current
# window aspect ratio we want
ar = 16/9
# large window width
largew = 1280
# ... and height
largeh = int(largew/ar)
# layouts to start with
layout_tiled = 6
layout_pip = 1
# enable debug output
do_debug = True


###
### other globals
###

# current home directory
home = os.environ['HOME']
# the fifo this script reads commands from
fifo = home + '/.mpvwincycle.fifo'
# we expect mpv sockets to be in this directory and to be named after
# PID
mpv_socket_dir = home + '/.config/mpv/socket/'
# the desktop/workspace we're actually operating on; this variable is assigned the
# current desktop number during operation if mpv_desktop == None
mpv_desktop_active = mpv_desktop

###
### diagnostic helpers
###

def debug(arg):
    if not do_debug: return
    print('Debug: ' + str(arg), file=sys.stderr)

def debug_obj(o):

    if not do_debug: return

    def indent(text, indent=8):
        fstring = 'Debug: ' + '{}'
        return ''.join([fstring.format(l) for l in text.splitlines(True)])
    def remove_keys(d):
        tmp = d.copy()
        for key in ['wins',
                    'wins_st',
                    'clients',
                    'clients_curfirst',
                    'clients_st',
                    'c_maxed',
                    'c_unmaxed',
                    's_layouts'
        ]:
            if key in tmp:
                #pass
                del tmp[key]
        return tmp

    print('Debug: >>> ' + type(o).__name__, file=sys.stderr)
    print(indent(pformat(remove_keys(vars(o)))), file=sys.stderr)
    print('Debug: <<< ', file=sys.stderr)

def warning(arg):
    print('Warning: ' + str(arg), file=sys.stderr)

def error(arg):
    print('Error: ' + str(arg), file=sys.stderr)


###
### general helpers
###

def rotate_list(l, n):
    return l[n:] + l[:n]

# signal handler for daemonized mode
def shutdown(signum, frame):
    sys.exit(0)


##########
###
### our classes
###
##########


###
### representation of an mpv window
###
class MPVClient:

    ### initializer does all the heavy lifting; acquires all window
    ### data from window manager, opens sockets
    ###
    def __init__(self, s, w):

        assert s # screen object (our class)
        assert w # window object (ewmh/xlib)

        self.base_init = False
        self.sock_init = False
        self.muted     = True

        try:

            ###
            ### general window data

            self.win  = w # the window object
            self.pid  = s.e.getWmPid(w)
            self.name = s.e.getWmName(w).decode("utf8", "strict")
            debug('Initializing client: ' + self.name)

            ###
            ### geometry

            # window geometry, use for width/height
            wg = w.get_geometry()
            # outer frame geometry, use for x/y postioning
            fg = self.frame(w, s.e.root).get_geometry()

            self.x     = fg.x
            self.y     = fg.y
            self.w     = wg.width
            self.h     = wg.height
            self.wdiff = fg.width - wg.width # diff between outer frame/win width
            self.hdiff = fg.height - wg.height # diff between outer frame/win height

            # individual border widths/heights
            self.lb_w  = wg.x # left border width (position of win inside parent frame)
            self.tb_h  = wg.y # top border height
            self.bb_h  = fg.height - wg.height - wg.y # bottom border height
            self.rb_w  = fg.width - wg.width - wg.x # right border width

            debug('Window : x:{:>4} y:{:>4} w:{:>4} h:{:>4}'.format(wg.x, wg.y, wg.width, wg.height))
            debug('Frame  : x:{:>4} y:{:>4} w:{:>4} h:{:>4}'.format(fg.x, fg.y, fg.width, fg.height))
            debug('Diffs  : w:{:>4} h:{:>4}'.format(self.wdiff, self.hdiff))

            ###
            ### window state

            self.states = list(s.e.getWmState(w, True))
            # horizontally maximized
            self.mh = ('_NET_WM_STATE_MAXIMIZED_HORZ' in self.states) or fg.width == s.wa_w
            # vertically maximized
            self.mv = ('_NET_WM_STATE_MAXIMIZED_VERT' in self.states) or fg.height == s.wa_h
            # maximized
            self.m = self.mh and self.mv
            # fullscreen
            self.f = '_NET_WM_STATE_FULLSCREEN' in self.states
            # on top
            self.t = '_NET_WM_STATE_ABOVE' in self.states
            # hidden
            self.hidden = '_NET_WM_STATE_HIDDEN' in self.states

            ###
            ### basic initialization done

            self.base_init = True

        except:
            raise

        try:

            ###
            ### sockets

            self.socket = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            self.socket.connect(mpv_socket_dir + str(self.pid))
            self.socket.setblocking(0)

            ###
            ### socket initialization done

            self.sock_init = True

        except:

            traceback.print_exc(file=sys.stdout)
            warning('exception in client socket construction, continuing')
            pass


    ### return True if this object is 'usable' in some sense
    ###
    def __bool__(self):
        return self.base_init # and self.sock_init ?


    ### non-tiling window managers generally reparent, i.e. put the
    ### application window into a larger, outer one to be able to draw
    ### decorations around it; this method retrieves that outer window
    ### for a given application window, to later get its x/y
    ### coordinates for positioning
    ###
    @staticmethod
    def frame(w, root):
        frame = w
        while frame.query_tree().parent != root:
            frame = frame.query_tree().parent
            return frame


###
### representation of a list of mpv client windows; the bulk of script
### code logic goes here
###
class MPVClientList:

    ### mpv mute/unmute socket messages
    ###
    getmute_msg   = b'{ "command": ["get_property", "mute"] }\n'
    setmute_msg   = b'{ "command": ["set_property", "mute", true] }\n'
    setunmute_msg = b'{ "command": ["set_property", "mute", false] }\n'


    ### build a list of MPVClient wrapper classes for all mpv windows,
    ### with supporting data we need for code logic
    ###
    def __init__(self, s=None):

        assert s # screen object

        try:

            self.full_init   = False
            self.have_socks  = True
            self.inc         = 0

            self.s      = s
            self.active = s.actclass == 'mpv' and s.desktop == mpv_desktop_active

            ###
            ### mpv windows in _NET_CLIENT_LIST order (= order in
            ### which windows were mapped)

            self.wins        = [w for w in s.wins
                                if w.get_wm_class() and w.get_wm_class()[1] == 'mpv'
                                and s.e.getWmDesktop(w) == mpv_desktop_active]
            self.num_wins    = len(self.wins)
            # our wrapper classes around windows
            self.clients     = [MPVClient(s, w) for w in self.wins]
            self.num_clients = len(self.clients)
            # windows in any kind of maximized state, for later reference
            self.c_maxed     = [c for c in self.clients if c.m or c.mh or c.mv]
            self.c_unmaxed   = [c for c in self.clients if c not in self.c_maxed]
            # max sizes of window decorations/borders we have seen
            self.wdiff       = max([c.wdiff for c in self.clients] + [0])
            self.hdiff       = max([c.hdiff for c in self.clients] + [0])

            # checks
            if self.num_wins <= 0: return
            if self.num_clients < self.num_wins:
                error('client class creation trouble')
                return
            num_baseinit = len([c for c in self.clients if c.base_init == True])
            if num_baseinit < self.num_wins:
                error('client class basic initialization trouble')
                return
            num_sockinit = len([c for c in self.clients if c.sock_init == True])
            if num_sockinit < self.num_wins:
                warning('mpv socket initialization trouble')
                self.have_socks = False

            ###
            ### mpv windows in _NET_CLIENT_LIST_STACKING order (bottom
            ### first)

            self.wins_st    = [w for w in s.wins_st
                               if w.get_wm_class() and w.get_wm_class()[1] == 'mpv'
                               and s.e.getWmDesktop(w) == mpv_desktop_active]
            self.clients_st = sorted(self.clients, key=lambda c: self.wins_st.index(c.win))

            ###
            ### retrieve mute status from mpv processes

            clients_unmuted = None
            if self.have_socks and self.get_set_mute_status():
                clients_unmuted = [c for c in self.clients_st if c.muted == False]

            ###
            ### define 'current' mpv window

            self.c_audio = None
            if clients_unmuted:
                # topmost unmuted window, if available (we did use
                # clients_st above for a reason)
                self.c_audio = clients_unmuted[-1]
                index  = self.clients_st.index(self.c_audio)
            elif self.active:
                # if an mpv window has the focus, pick that
                index = self.wins_st.index(s.actwin)
            else:
                # just pick the topmost window
                index = -1

            self.current          = self.clients_st[index]
            self.curindex         = self.clients.index(self.current)
            self.clients_curfirst = rotate_list(self.clients, self.curindex)
            debug("current: " + self.current.name)

            ###
            ### active window, if available; we need that if we want
            ### to shift window focus only

            self.actindex = None
            self.c_act = None
            if self.active:
                self.actindex = self.wins.index(s.actwin)
                self.c_act    = self.clients[self.actindex]

            self.full_init = True

        except:
            error('MPVClientList initialization trouble')
            raise


    ###
    ### helper methods
    ###


    ### return usability status
    ###
    def __bool__(self):
        return self.full_init


    ### ...
    ###
    def __len__(self):
        return len(self.clients)


    ### list of clients, current first
    ###
    def c_curfirst(self, clist=None):

        c     = self.current
        clist = clist or self.clients

        if c in clist:
            return rotate_list(clist, clist.index(c))
        else:
            return clist # fallback


    ### next window after/before current window, depending on
    ### increment
    ###
    def new_current(self, inc):
        if self.current and self.current in self.clients:
            i = self.clients.index(self.current)
            return rotate_list(self.clients, inc)[i]
        else:
            return None


    ### next active (focused) window, if any
    ###
    def new_act(self, inc):
        if not self.active: return None
        if self.c_act and self.c_act in self.clients:
            i = self.clients.index(self.c_act)
            return rotate_list(self.clients, inc)[i]
        else:
            return None


    ### move unmute status
    ###
    def rotate_audio(self):
        c = self.new_current(self.inc)
        if not self.have_socks or not c: return
        self.get_set_mute_status(c)
        self.c_act = self.current # focus follow audio!


    ### move focus
    ###
    def rotate_focus(self):
        c = self.new_act(self.inc)
        if c: self.s.e.setActiveWindow(c.win)


    ###
    ### layout reset methods
    ###


    ### helper: reset all windows into an unmaximized, non fullscreen
    ### and non on-top state
    ###
    def reset_window_states(self, clist = None):

        clist = clist or self.c_curfirst()
        for c in clist:
            self.s.e.setWmState(c.win, 0, '_NET_WM_STATE_FULLSCREEN')
            self.s.e.setWmState(c.win, 0, '_NET_WM_STATE_MAXIMIZED_VERT', '_NET_WM_STATE_MAXIMIZED_HORZ')
            self.s.e.setWmState(c.win, 0, '_NET_WM_STATE_ABOVE', '_NET_WM_STATE_BELOW')
            self.s.e.setWmState(c.win, 0, '_NET_WM_STATE_SHADED', '_NET_WM_STATE_HIDDEN')


    ### our basic window layouts we can fall back to if things get
    ### messed up
    ###
    def reset(self, pip=False):

        #debug("reset w/ layout: {0}".format(layout))

        self.reset_window_states()
        clist = self.c_curfirst()

        if pip:
            l = Layouter(self.s, self.wdiff, self.hdiff, layout_pip, True)
        else:
            l = Layouter(self.s, self.wdiff, self.hdiff, layout_tiled, False)
        debug_obj(l)
        ls = l.yield_small_geometries()

        if not pip:
            # the current window is made to be the 'large' one
            c = self.current
            debug('reset large: ' + c.name)
            x, y = l.l_layouts[int(layout_tiled/2)]
            w, h = l.l
            self.s.e.setMoveResizeWindow(c.win, 0, x, y, w, h)
            clist = clist[1:]

        for c in reversed(clist):
            debug('reset small: ' + c.name)
            x, y, w, h = next(ls)
            self.s.e.setMoveResizeWindow(c.win, 0, x, y, w, h)
            if self.active:
                c.win.configure(stack_mode=X.Above)

        if pip:
            if self.active:
                self.s.e.setWmState(c.win, 1, '_NET_WM_STATE_MAXIMIZED_VERT', '_NET_WM_STATE_MAXIMIZED_HORZ')
                if len(self) > 1:
                    self.s.e.setWmState(self.c_curfirst()[-1].win, 1, '_NET_WM_STATE_ABOVE')
            else:
                self.s.e.setWmState(self.current.win, 1, '_NET_WM_STATE_ABOVE')


    def reset_tile(self):
        self.reset(False)

    def reset_pip(self):
        self.reset(True)


    ###
    ### toggle methods
    ###


    ### limit client list to topmost 2 windows, resp. to topmost and
    ### topmost maximized if one exists
    ###
    def limit_to_top(self):

        if len(self) <= 1: return

        c     = self.current
        top   = self.clients_st[-1]
        maxed = [c for c in self.clients_st if c.m]

        if c == top:
            if c.m:
                # windows below current
                cc = self.clients_st[-2]
            else:
                # topmost maxed if existent, else window below current
                cc = maxed[-1] if len(maxed) > 0 else self.clients_st[-2]
        else:
            cc = top

        # hackish, technically we should update all attributes derived
        # from 'clients'; purpose is to limit client list for
        # audio/focus shift, too; otherwise we could throw all the
        # code into toggle_top()
        self.clients = [c, cc]


    ### perform a window state shift/geometry rotation on the two
    ### windows defined in limit_to_top()
    ###
    def toggle_top(self):

        if len(self) <= 1: return

        # cc is going to be new current
        c,cc = self.clients[:2]

        if cc.t:
            self.s.e.setWmState(cc.win, 0, '_NET_WM_STATE_ABOVE')
            self.s.e.setWmState(c.win, 1, '_NET_WM_STATE_ABOVE')
        elif c.t:
            self.s.e.setWmState(c.win, 0, '_NET_WM_STATE_ABOVE')
            self.s.e.setWmState(cc.win, 1, '_NET_WM_STATE_ABOVE')

        if c in self.c_maxed:
            self.shift_max_states(c, cc)
        elif cc in self.c_maxed:
            self.shift_max_states(cc, c)
        else:
            self.rotate([c, cc])


    ###
    ### window layout 'rotation' methods
    ###


    ### main window rotation method; if current window is fullscreen
    ### or maximized we just shift the state; otherwise we perform a
    ### full geometry rotation
    ###
    def rotate_or_shift(self):

        c  = self.current
        cc = self.new_current(self.inc)
        t  = self.clients_st[-1]

        if not cc: return

        if c.f: # fullscreen
            shift_fc_state(self, c, cc)

        # c is maxed but not the topmost
        elif c.m and c != t and len(self.c_unmaxed) > 1:
            self.clients = self.c_unmaxed
            self.rotate(self.c_unmaxed)

        # c or cc maxed, possibly both
        elif c.f:
            self.shift_fc_state(c, cc)

        elif c in self.c_maxed or (cc in self.c_maxed and len(self.c_unmaxed) <= 1):

            # after this call, cc is maxed, c unmaxed
            if not c in self.c_maxed: c,cc = cc,c
            self.shift_max_states(c, cc)

            # put unmaxed c in top layer if cc was
            if cc.t:
                self.s.e.setWmState(cc.win, 0, '_NET_WM_STATE_ABOVE')
                self.s.e.setWmState(c.win, 1, '_NET_WM_STATE_ABOVE')

        # current is not maxed, and there are more unmaxed windows; we
        # perform a full geometry rotation, but only on unmaxed
        # windows
        else:
            self.clients = self.c_unmaxed
            self.rotate(self.c_unmaxed)


    ### full geometry rotation proper
    ###
    def rotate(self, clist=None, inc=0):

        if not clist: clist=self.c_curfirst()
        if len(clist) <= 1: return

        if not inc: inc = self.inc
        pairs = list(zip(rotate_list(clist, inc), clist))

        # we include shifting above state into rotation, but do this
        # before/after rotation to hopefulle reduce visual noise
        for c in [c for (c,d) in pairs if c.t]:
            self.s.e.setWmState(c.win, 0, '_NET_WM_STATE_ABOVE')
        for (c,d) in pairs:
            self.shift_geometry(c, d)
        for c in [c for (c,d) in pairs if d.t]:
            self.s.e.setWmState(c.win, 1, '_NET_WM_STATE_ABOVE')


    ### fullscreen state shifting helper
    ###
    def shift_fc_state(self, c, cc):
        if not (c.f or cc.f): return
        if not c.f: c,cc = cc,c
        self.s.e.setWmState(c.win, 0, '_NET_WM_STATE_FULLSCREEN')
        self.s.e.setWmState(cc.win, 1, '_NET_WM_STATE_FULLSCREEN')


    ### maximized state shifting helper
    ###
    def shift_max_states(self, c, cc):
        if not (c in self.c_maxed or cc in self.c_maxed): return
        if not c in self.c_maxed: c,cc = cc,c
        if c.m:
            self.s.e.setWmState(cc.win, 1, '_NET_WM_STATE_MAXIMIZED_VERT', '_NET_WM_STATE_MAXIMIZED_HORZ')
            if self.active:
                cc.win.configure(stack_mode=X.Above)
            self.s.e.setWmState(c.win, 0, '_NET_WM_STATE_MAXIMIZED_VERT', '_NET_WM_STATE_MAXIMIZED_HORZ')
        elif c.mh:
            self.s.e.setWmState(cc.win, 1, '_NET_WM_STATE_MAXIMIZED_HORZ')
            self.s.e.setWmState(c.win, 0, '_NET_WM_STATE_MAXIMIZED_HORZ')
        elif c.mv:
            self.s.e.setWmState(cc.win, 1, '_NET_WM_STATE_MAXIMIZED_VERT')
            self.s.e.setWmState(c.win, 0, '_NET_WM_STATE_MAXIMIZED_VERT')


    ### window geometry shifting helper; c is moved into the place of
    ### cc
    ###
    def shift_geometry(self, c, cc):
        self.s.e.setMoveResizeWindow(c.win, 0, cc.x, cc.y, cc.w, cc.h)


    ###
    ### mpv socket communication related methods
    ###


    ### mpv socket messaging method, for mute/unmute
    ###
    def get_set_mute_status(self, current=None):

        # client parameter means unmute this one; else just get status
        if current:
            # mute first, then unmute
            clist   = [ c for c in self.clients if c != current ] + [current]
            msgs = (len(clist) - 1) * [self.setmute_msg] + [self.setunmute_msg]
        else:
            clist = self.clients
            msgs = len(clist) * [self.getmute_msg]

        debug('socket wins: ' + str([c.name for c in clist]))
        debug('socket msgs: ' + str(msgs))

        sockets = [c.socket for c in clist]
        msd = MPVSockDispatcher(zip(sockets, msgs))
        debug('socket rslt: ' + str(msd.result))

        if not msd:
            error('mpv socket communication error')
            return False

        if current:
            for c in clist:
                c.muted = True
            current.muted = False
        else:
            for i in range(0, len(clist)):
                clist[i].muted = msd.result[i]['data']

        return True


    ### we close all sockets after each run
    ###
    def close_sockets(self):
        for c in self.clients:
            if getattr(c, "socket", None) and c.socket and c.socket.fileno() != -1:
                debug("closing socket for window: " + str(c.name))
                c.socket.close()


    ### method to test xlib/ewmh behavior
    ###
    def test(self):
        c  = self.current
        #self.s.e.setMoveResizeWindow(c.win, X.SouthWestGravity, None, None, None, None)
        #c.win.change_attributes(win_gravity=X.NorthGravity, bit_gravity=0)
        #c.win.set_wm_normal_hints(flags = 0, win_gravity = X.SouthEastGravity, bit_gravity=X.SouthEastGravity)
        #self.s.e.root.change_attributes(win_gravity=X.NorthWestGravity)
        self.s.e.setMoveResizeWindow(c.win, X.StaticGravity|1<<8|1<<9|1<<10|1<<11,\
                                     self.s.wa_w - largew, 0,\
                                     largew, largeh)


###
### mpv socket communication helper class
###
class MPVSockDispatcher():

    def __init__(self, requests = None):
        self.ok     = False
        self.result = None
        if requests:
            self.__call__(requests)


    def __bool__(self):
        return self.ok


    ### dispatch messages to a list of mpv sockets, read return
    ### values; expects a list of tuples
    ### request = [(socket1,msg1), (socket2,msg2), ... ]
    ###
    def __call__(self, requests = None):

        self.ok     = False
        self.result = None

        if not requests: return

        sockets, msgs = zip(*requests)
        inputs        = list(sockets)
        outputs       = list(sockets)
        n_sockets     = len(sockets)
        retlist       = n_sockets * [None]

        try:

            t_end = time.time() + 3
            # give up after 3 seconds max, if necessary
            while (inputs or outputs) and time.time() < t_end:

                readable, writable, exceptional = select.select(inputs, outputs, inputs, 1)

                if not (readable or writable):
                    error('socket select timeout')
                    break
                for s in writable:
                    msg = msgs[sockets.index(s)]
                    s.sendall(msg)
                    outputs.remove(s)
                for s in readable:
                    ret = s.recv(1014).decode("utf8", "strict").rstrip()
                    # unrelated event messages may be pushed to our socket by mpv; so keep reading 
                    # until a message arrives that looks like a valid response to our request
                    ret = re.findall(r'{[^}]*"error":[^}]*}', ret)
                    if ret:
                        # we evaluate the returned json as a literal
                        # python dictionary; this will probably croak with
                        # operations other than set/unset mute
                        retlist[sockets.index(s)] = eval(ret[0].replace('true','True').replace('false','False'))
                        # done reading on this socket
                        inputs.remove(s)

            n_success = sum([1 for r in retlist if r and r['error'] == 'success'])
            self.ok = n_success == n_sockets

            if self.ok:
                self.result = retlist
            else:
                if inputs:
                    error('input socket communication failure')
                elif outputs:
                    error('output socket communication failure')
                else:
                    error('socket communication failure')

        except:
            traceback.print_exc(file=sys.stdout)
            pass


###
### Class that calculates window geometries/positions for the various layouts
###
class Layouter:

    ### collapse means don't distribute small windows across work area but
    ### rather put them all (i.e. collapse them all into) the same position;
    ### this is True for PIP layouts
    ###
    def __init__(self, screen=None, wdiff=0, hdiff=0, l = 0, collapse = False):

        assert(screen)

        self.s        = screen
        self.wdiff    = wdiff   # window border decoration width, sum of both sides
        self.hdiff    = hdiff   # window border decoration height, sum of both sides
        self.layout   = l       # layout number
        self.collapse = collapse # whether to collapse all small windows into one position,
                                 # for pip layout

        ###
        ### we now calculate the dimensions of the smaller windows, given the
        ### screen space and the dimensions of the large one; this calculation
        ### includes border decorations

        # height of (inner) small window in a top/down arrangement w/ respect to large window
        # the small windows are then arranged horizontally
        h_h = self.s.wa_h - (largeh + 2 * self.hdiff)
        # according width of small window
        h_w = int(h_h * ar)
        # width of (inner) small window in a left/right arrangement w/ respect to large window
        # the small windows are then arranged vertically
        v_w = self.s.wa_w - (largew + 2 * self.wdiff)
        # according height of small window
        v_h = int(v_w / ar)

        self.h = [h_w, h_h] # inner frame dimensions for horizontally arranged small windows
        self.v = [v_w, v_h] # inner frame dimensions for vertically arranged small windows
        self.H = [h_w + wdiff, h_h + hdiff] # according outer frame dimensions
        self.V = [v_w + wdiff, v_h + hdiff] # according outer frame dimensions
        self.l = [largew, largeh] # inner frame dimensions of large window
        self.L = [largew + wdiff, largeh + hdiff] # outer frame dimensions of large window

        # the 4 possible positions of the large window in the work area
        self.l_layouts = [
            # bottom left
            [self.s.wa_x, self.s.wa_y + self.s.wa_h - self.L[1]],
            # bottom right
            [self.s.wa_x + self.s.wa_w - self.L[0] , self.s.wa_y + self.s.wa_h - self.L[1]],
            # top left
            [self.s.wa_x, self.s.wa_y],
            # top right
            [self.s.wa_x + self.s.wa_w - self.L[0] , self.s.wa_y]
        ]

        # parameters for _h,_v calls (even array entries) or _v,_h calls (odd array entries)
        self.s_layouts = [

            ###
            ### the following comments describe how small windows are arranged, in terms of
            ### - whether they are arranged in horizontal or vertical fashion
            ### - work area border where the first window is placed (top, bottom, left, right)
            ### - direction of window arrangement.
            ### Horizontal or vertical is determined by the array index (see yield_small_geometries);
            ### even index means horizontal, odd vertical.

            [[True, True],                        [False, True]],
            # vertical, right, bottom to top,     then horizontal, top, right to left
            [[False, False],                      [ False, True]],
            # horizontal, top, right to left,     then vertical, left, top to bottom
            [[False, True],                       [True, True]],
            # vertical, left, bottom up,          then horizontal, top, left to right
            [[True, False],                       [True, True]],
            # horizontal, bottom, left to right,  then vertical, right, bottom to top
            [[True, False],                       [False, False]],
            # vertical, right, top down,          then horizontal, bottom, right to left
            [[False, True],                       [False, False]],
            # horizontal, bottom, right to left,  then vertical, left, bottom to top
            [[False, False],                      [True, False]],
            # vertical, left, top down,           then horizontal, bottom, left to right
            [[True, True],                        [True, False]]
        ]

    ### consecutively yield geometries of windows according to current layout;
    ### user interface of this class
    ###
    def yield_small_geometries(self):

        a,b = self.s_layouts[self.layout]

        if self.layout % 2 == 0:
            # arrange windows horizontally first, then vertically
            C = chain(self._h(*a), self._v(*b, True))
        else:
            # arrange windows vertically first, then horizontally
            C = chain(self._v(*a), self._h(*b, True))
        for c in C:
            yield c

    ### consecutively yield geometries of vertically arranged windows;
    ### keep_going means continue yielding geometries even if work area space is
    ### filled up
    ###
    def _v(self, left=True, top=True, keep_going = False):

        # horizontal position of all windows, either left or right border of work area
        x = self.s.wa_x if left else self.s.wa_x + self.s.wa_w - self.V[0]

        # vertical position we begin with, either top or bottom of work area
        Y = [self.s.wa_y, self.s.wa_y + self.s.wa_h - self.V[1]]
        # max vertical screen space we're going to fill up, in terms of where
        # the edge of a window goes
        Ymax = self.s.wa_h - self.V[1]/2

        # if keep_going is true we're on the tail end of a _h,_v call, so leave room for
        # horizontally arranged windows
        if keep_going:
            Y = [ Y[0] + self.H[1], Y[1] - self.H[1]]
            Ymax -= self.H[1]

        # vertical starting position
        y = Y[0] if top else Y[1]
        # direction of progress
        sign = 1 if top else -1
        # in pip layout (collapse true) we don't offset windows at all
        offset = 0 if self.collapse else self.V[1]

        total = 0
        while total < Ymax or keep_going:
            # make sure y is set so that the window stays within the work area
            y = min( max( self.s.wa_y, y ), self.s.wa_y + self.s.wa_h - self.V[1] )
            yield [x, y, self.v[0], self.v[1]]
            y += sign * offset
            total += offset

    ### consecutively yield geometries of horizontally arranged windows;
    ### keep_going means continue yielding geometries even if work area space is
    ### filled up
    ###
    def _h(self, left = True, top = True, keep_going = False):

        # vertial position of all windows, either top or right bottom of work area
        y = self.s.wa_y if top else self.s.wa_y + self.s.wa_h - self.H[1]

        # horizontal position we begin with, either at left or right border of work area
        X = [self.s.wa_x, self.s.wa_x + self.s.wa_w - self.H[0]]
        # max horizonantal screen space we're going to fill up, in terms of where
        # the edge of a window goes
        Xmax = self.s.wa_w - self.H[0]/2

        # if keep_going is true we're on the tail end of a _v,_h call, so leave room for
        # vertically arranged windows
        if keep_going:
            X = [ X[0] + self.V[0], X[1] - self.V[0]]
            Xmax -= self.V[0]

        # horizontal starting position
        x = X[0] if left else X[1]
        # direction of progress
        sign = 1 if left else -1
        # in pip layout (collapse true) we don't offset windows at all
        offset = 0 if self.collapse else self.H[0]

        total = 0
        while total < Xmax or keep_going:
            # make sure x is set so that the window stays within the work area
            x = min( max( self.s.wa_x, x ), self.s.wa_x + self.s.wa_w - self.H[0] )
            yield [x, y, self.h[0], self.h[1]]
            x += sign * offset
            total += offset


###
### wrapper class around ewmh object; stores screen state, like
### dimensions of work area, current desktop, active window, etc.
###
class Screen:

    def __init__(self, e=None):

        assert e

        self.e = e

        try:
            # get general state from window manager
            self.desktop  = e.getCurrentDesktop()
            self.workarea = e.getWorkArea()
            self.actwin   = e.getActiveWindow() # currently active window
            self.actname  = e.getWmName(self.actwin) # its class
            self.actclass = self.actwin.get_wm_class()[1] if self.actwin and self.actwin.get_wm_class() else None # its class
            self.wins     = e.getClientList() # all windows in normal order
            self.wins_st  = e.getClientListStacking() # all windows in stacking order

        except Exception as exc:
            error('wm communication error: ' + str(exc))
            raise

        ###
        ### work area geometry; this is screen size minus dock areas
        ### and/or padding

        self.wa_x = self.workarea[self.desktop * 4]     # horizontal padding
        self.wa_y = self.workarea[self.desktop * 4 + 1] # vertical padding
        self.wa_w = self.workarea[self.desktop * 4 + 2] # width
        self.wa_h = self.workarea[self.desktop * 4 + 3] # height


###
### representation of a user command we're supposed to execute
###
class Command:

    def __init__(self):

        self.inc         = 0
        self.next_l_tile = False
        self.next_l_pip  = False
        self.reset_tile  = False
        self.reset_pip   = False
        self.toggle_top  = False
        self.focus_only  = False
        self.audio_only  = False


###
### helper class, holds code to read user commands from fifo
###
class CommandReader:

    def __init__(self, f=fifo):

        assert f
        self.f = f
        self.input = None

        try:
            os.mkfifo(self.f)
        except OSError as oe:
            if oe.errno != os.errno.EEXIST:
                error("CommandReader: can't create communication fifo: " + self.f)
                raise

    def get_next(self):

        with open(self.f) as f:
            self.input = f.read().rstrip()

        if not self.input:
            warning("CommandReader: empty input on fifo read")
            return None

        cmd = Command()

        if   self.input[0] == 'n': cmd.inc          = -1    # next
        elif self.input[0] == 'p': cmd.inc          = 1     # previous
        elif self.input[0] == 'l': cmd.next_l_tile  = True  # next layout, reset
        elif self.input[0] == 'L': cmd.next_l_pip   = True  # next layout, reset
        elif self.input[0] == 'r': cmd.reset_tile   = True  # reset
        elif self.input[0] == 'R': cmd.reset_pip    = True  # reset
        elif self.input[0] == 't':                          # toggle top
            cmd.toggle_top = True
            cmd.inc = 1
        else:
            warning("CommandReader: input not recognized: " + self.input)
            return None

        if len(self.input) > 1 and self.input[1] == 'f': cmd.focus_only = True
        if len(self.input) > 1 and self.input[1] == 'a': cmd.audio_only = True

        return cmd


###
### main loop function
###
def main():

    e  = ewmh.EWMH()
    cr = CommandReader()

    global mpv_desktop_active
    global layout_tiled
    global layout_pip

    while True:

        try:

            # we don't want to get hammered, nor do we want to hammer
            # the mpv processes with mute/unmute requests
            sleep(0.25)

            cmd = cr.get_next()
            debug_obj(cr)
            if not cmd:
                error('main: get_next command failure')
                continue
            debug_obj(cmd)

            s = Screen(e)
            debug_obj(s)

            # we can choose to manage windows on one fixed desktop
            # only, even when we're currently on another one; or
            # always manage mpv windows on the current desktop only;
            # 'None' means always manage windows only on current
            # desktop
            if mpv_desktop == None: mpv_desktop_active = s.desktop

            mpv_list = MPVClientList(s)
            if not mpv_list:
                error('main: mpv list initialization trouble, stopping iteration')
                continue

            mpv_list.inc = cmd.inc

            # limit client list to top windows if we're just toggling
            if cmd.toggle_top: mpv_list.limit_to_top()
            debug_obj(mpv_list)

            # the mpv_list methods we are going to execute in
            # succession
            call_list = []
            call_list.append(mpv_list.rotate_focus) # move focus

            if not cmd.focus_only:
                call_list.append(mpv_list.rotate_audio) # move unmute status
                if not (cmd.audio_only or s.desktop != mpv_desktop_active):
                    if cmd.next_l_tile :
                        layout_tiled = (layout_tiled + 1) % 8
                        func = mpv_list.reset_tile
                    elif cmd.next_l_pip :
                        layout_pip = (layout_pip + 1) % 8
                        func = mpv_list.reset_pip
                    elif cmd.reset_tile  : func = mpv_list.reset_tile
                    elif cmd.reset_pip   : func = mpv_list.reset_pip
                    elif cmd.toggle_top  : func = mpv_list.toggle_top
                    #elif cmd.toggle_top : func = mpv_list.test
                    else                 : func = mpv_list.rotate_or_shift
                    call_list.append(func)

            # do window manipulation first, then audio, then focus;
            # implementation depends on this order
            for f in reversed(call_list): f()

        except (KeyboardInterrupt, SystemExit):
            raise
        except:
            traceback.print_exc(file=sys.stdout)
            pass
        finally:
            if s and getattr(s, "e", None) and s.e:
                s.e.display.flush()
            mpv_list.close_sockets()
            debug(80 * '-')
            debug('')


###
### let's roll
###
if __name__ == "__main__":

    # don't detach from terminal when in debug mode
    if do_debug:
        main()
    # else daemonize this process
    else:
        with daemon.DaemonContext(signal_map={signal.SIGINT: shutdown, signal.SIGTERM: shutdown}):
            main()
