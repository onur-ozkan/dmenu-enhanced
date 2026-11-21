/* See LICENSE file for copyright and license details. */
#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <locale.h>
#include <math.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <time.h>
#include <unistd.h>

#include <X11/Xlib.h>
#include <X11/Xatom.h>
#include <X11/Xutil.h>
#ifdef XINERAMA
#include <X11/extensions/Xinerama.h>
#endif
#include <X11/Xft/Xft.h>

#include "drw.h"
#include "util.h"

/* macros */
#define INTERSECT(x,y,w,h,r)  (MAX(0, MIN((x)+(w),(r).x_org+(r).width)  - MAX((x),(r).x_org)) \
                             * MAX(0, MIN((y)+(h),(r).y_org+(r).height) - MAX((y),(r).y_org)))
#define LENGTH(X)             (sizeof X / sizeof X[0])
#define NUMBERSMAXDIGITS      100
#define NUMBERSBUFSIZE        (NUMBERSMAXDIGITS * 2) + 1

/* enums */
enum
{ SchemeNorm, SchemeSel, SchemeNormHighlight, SchemeSelHighlight,
	SchemeOut, SchemeMid, SchemeLast
};								/* color schemes */


struct item
{
	char *text;
	struct item *left, *right;
	int out;
	int width;
	double distance;
};

static char numbers[NUMBERSBUFSIZE] = "";
static char text[BUFSIZ] = "";
static char *embed;
static int bh, mw, mh;
static int inputw = 0, promptw, numbersw;
static int lrpad;				/* sum of left and right padding */
static size_t cursor;
static size_t itemcount, matchcount;
static struct item *items = NULL;
static struct item *matches, *matchend;
static struct item *prev, *curr, *next, *sel;
static int mon = -1, screen;

static Atom clip, utf8;
static Display *dpy;
static Window root, parentwin, win;
static XIC xic;

static Drw *drw;
static Clr *scheme[SchemeLast];

#include "config.h"

static int (*fstrncmp)(const char *, const char *, size_t) = strncmp;
static char *(*fstrstr)(const char *, const char *) = strstr;

static size_t runelen(const char *s)
{
	unsigned char c = *s;
	size_t len = c >= 0xf0 && c <= 0xf4 ? 4 : c >= 0xe0 && c <= 0xef ? 3 :
		c >= 0xc2 && c <= 0xdf ? 2 : 1;
	for (size_t i = 1; i < len; i++)
		if ((s[i] & 0xc0) != 0x80)
			return 1;
	return len;
}

static int textw(const char *s)
{
	unsigned int width = drw_fontset_getwidth(drw, s);
	return width > (unsigned int)(INT_MAX - lrpad) ? INT_MAX : (int)width + lrpad;
}

static void appenditem(struct item *item, struct item **list, struct item **last)
{
	if (*last)
		(*last)->right = item;
	else
		*list = item;

	item->left = *last;
	item->right = NULL;
	*last = item;
}

static void calcoffsets(void)
{
	size_t i, n;

	if (lines > 0)
		n = (size_t)lines *columns;
	else
		n = MAX(1, mw - promptw - inputw - textw("<") - textw(">") - numbersw);
	/* calculate which items will begin the next page and previous page */
	for (i = 0, next = curr; next; next = next->right)
		if ((i += lines ? 1 : MIN((size_t)next->width, n)) > n)
			break;
	for (i = 0, prev = curr; prev && prev->left; prev = prev->left)
		if ((i += lines ? 1 : MIN((size_t)prev->left->width, n)) > n)
			break;
}

static void cleanup(void)
{
	size_t i;

	XUngrabKeyboard(dpy, CurrentTime);
	for (i = 0; i < SchemeLast; i++)
		free(scheme[i]);
	drw_free(drw);
	XSync(dpy, False);
	XCloseDisplay(dpy);
	FcFini();
}

static char *cistrstr(const char *s, const char *sub)
{
	size_t len;

	for (len = strlen(sub); *s; s += runelen(s))
		if (!strncasecmp(s, sub, len))
			return (char *)s;
	return NULL;
}

static int highlight(struct item *item, char *start, size_t len, int x, int y, int maxw)
{
	int indent, width;
	char saved = *start;

	*start = '\0';
	indent = textw(item->text) - lrpad;
	*start = saved;
	if (indent > maxw)
		return 0;
	saved = start[len];
	start[len] = '\0';
	width = textw(start) - lrpad;
	if (width <= maxw - indent)
		drw_text(drw, x + lrpad / 2 + indent, y, width, bh, 0, start, 0);
	start[len] = saved;
	return width <= maxw - indent;
}

static void drawhighlights(struct item *item, int x, int y, int maxw)
{
	char buf[sizeof text], *token, *start, *p = text;
	size_t len, plen;

	if (!*text)
		return;
	maxw -= lrpad / 2;
	if (item->width > maxw + lrpad / 2)
		maxw -= textw("...") - lrpad;
	drw_setscheme(drw, scheme[item == sel ? SchemeSelHighlight : SchemeNormHighlight]);
	if (fuzzy)
	{
		plen = runelen(p);
		for (start = item->text; *start && *p; start += len)
		{
			len = runelen(start);
			if (len == plen && !fstrncmp(start, p, len))
			{
				if (!highlight(item, start, len, x, y, maxw))
					return;
				p += plen;
				plen = runelen(p);
			}
		}
	}
	else
	{
		strcpy(buf, text);
		for (token = strtok(buf, " "); token; token = strtok(NULL, " "))
			for (start = item->text; (start = fstrstr(start, token)); start += len)
			{
				for (p = start, len = strlen(token); p < start + len; p += plen)
				{
					plen = runelen(p);
					if (!highlight(item, p, plen, x, y, maxw))
						break;
				}
				if (p < start + len)
					break;
			}
	}
}


static int drawitem(struct item *item, int x, int y, int w)
{
	int r;
	if (w <= 0)
		return x;
	if (item == sel)
		drw_setscheme(drw, scheme[SchemeSel]);
	else if (item->left == sel || item->right == sel)
		drw_setscheme(drw, scheme[SchemeMid]);
	else if (item->out)
		drw_setscheme(drw, scheme[SchemeOut]);
	else
		drw_setscheme(drw, scheme[SchemeNorm]);

	r = drw_text(drw, x, y, w, bh, lrpad / 2, item->text, 0);
	drawhighlights(item, x, y, w);
	return r;
}

static void drawmenu(void)
{
	int curpos;
	struct item *item;
	int x = 0, y = 0, fh = drw->fonts->h, w;

	drw_setscheme(drw, scheme[SchemeNorm]);
	drw_rect(drw, 0, 0, mw, mh, 1, 1);

	if (prompt && *prompt)
	{
		drw_setscheme(drw, scheme[SchemeSel]);
		x = drw_text(drw, x, 0, promptw, bh, lrpad / 2, prompt, 0);
	}
	/* draw input field */
	w = (lines || !matches) ? mw - x - numbersw : inputw;
	drw_setscheme(drw, scheme[SchemeNorm]);
	drw_text(drw, x, 0, w, bh, lrpad / 2, text, 0);

	curpos = textw(text) - textw(&text[cursor]);
	if ((curpos += lrpad / 2 - 1) >= 0 && curpos + 2 <= w)
	{
		drw_setscheme(drw, scheme[SchemeNorm]);
		drw_rect(drw, x + curpos, 2 + MAX(0, bh - fh) / 2, 2, MAX(0, MIN(fh - 4, bh - 4)), 1, 0);
	}

	if (lines > 0)
	{
		/* draw grid */
		int i = 0;
		for (item = curr; item != next; item = item->right, i++)
			drawitem(item,
					 x + ((i / lines) * ((mw - x) / columns)),
					 y + (((i % lines) + 1) * bh), (mw - x) / columns);
	}
	else if (matches)
	{
		/* draw horizontal list */
		x += inputw;
		w = textw("<");
		if (curr->left)
		{
			drw_setscheme(drw, scheme[SchemeNorm]);
			drw_text(drw, x, 0, w, bh, lrpad / 2, "<", 0);
		}
		x += w;
		for (item = curr; item != next; item = item->right)
			x = drawitem(item, x, 0, MIN(item->width, mw - x - textw(">") - numbersw));
		if (next)
		{
			w = textw(">");
			drw_setscheme(drw, scheme[SchemeNorm]);
			drw_text(drw, mw - w - numbersw, 0, w, bh, lrpad / 2, ">", 0);
		}
	}
	drw_setscheme(drw, scheme[SchemeNorm]);
	drw_text(drw, mw - numbersw, 0, numbersw, bh, lrpad / 2, numbers, 0);
	drw_map(drw, win, 0, 0, mw, mh);
}

static void grabfocus(void)
{
	struct timespec ts = {.tv_sec = 0,.tv_nsec = 10000000 };
	Window focuswin;
	int i, revertwin;

	for (i = 0; i < 100; ++i)
	{
		XGetInputFocus(dpy, &focuswin, &revertwin);
		if (focuswin == win)
			return;
		XSetInputFocus(dpy, win, RevertToParent, CurrentTime);
		nanosleep(&ts, NULL);
	}
	die("cannot grab focus");
}

static void grabkeyboard(void)
{
	struct timespec ts = {.tv_sec = 0,.tv_nsec = 1000000 };
	int i;

	if (embed)
		return;
	/* try to grab keyboard, we may have to wait for another process to ungrab */
	for (i = 0; i < 1000; i++)
	{
		if (XGrabKeyboard(dpy, DefaultRootWindow(dpy), True, GrabModeAsync,
						  GrabModeAsync, CurrentTime) == GrabSuccess)
			return;
		nanosleep(&ts, NULL);
	}
	die("cannot grab keyboard");
}

int compare_distance(const void *a, const void *b)
{
	struct item *da = *(struct item **)a;
	struct item *db = *(struct item **)b;

	if (!db)
		return 1;
	if (!da)
		return -1;

	return da->distance == db->distance ? 0 : da->distance < db->distance ? -1 : 1;
}

void fuzzymatch(void)
{
	/* bang - we have so much memory */
	struct item *it;
	struct item **fuzzymatches = NULL;
	size_t number_of_matches = 0, i, pidx, sidx, eidx, len, plen;
	size_t text_len = strlen(text);

	matches = matchend = NULL;

	/* walk through all items */
	for (it = items; it && it->text; it++)
	{
		if (text_len)
		{
			pidx = 0;			/* pointer */
			sidx = eidx = SIZE_MAX;	/* start of match, end of match */
			plen = runelen(text);
			/* walk through item text */
			for (i = 0; it->text[i]; i += len)
			{
				len = runelen(it->text + i);
				/* fuzzy match pattern */
				if (len == plen && !fstrncmp(text + pidx, it->text + i, len))
				{
					if (sidx == SIZE_MAX)
						sidx = i;
					pidx += plen;
					if (pidx == text_len)
					{
						eidx = i;
						break;
					}
					plen = runelen(text + pidx);
				}
			}
			/* build list of matches */
			if (eidx != SIZE_MAX)
			{
				/* add penalties for late starts and gaps between matching characters */
				it->distance = log((double)sidx + 2) + (double)(eidx - sidx) - text_len;
				appenditem(it, &matches, &matchend);
				number_of_matches++;
			}
		}
		else
		{
			appenditem(it, &matches, &matchend);
		}
	}

	if (number_of_matches)
	{
		/* initialize array with matches */
		if (!(fuzzymatches = realloc(fuzzymatches, number_of_matches * sizeof(struct item *))))
			die("cannot realloc %zu bytes:", number_of_matches * sizeof(struct item *));
		for (i = 0, it = matches; it && i < number_of_matches; i++, it = it->right)
		{
			fuzzymatches[i] = it;
		}
		/* sort matches according to distance */
		qsort(fuzzymatches, number_of_matches, sizeof(struct item *), compare_distance);
		/* rebuild list of matches */
		matches = matchend = NULL;
		for (i = 0; i < number_of_matches; i++)
		{
			appenditem(fuzzymatches[i], &matches, &matchend);
		}
		free(fuzzymatches);
	}
	matchcount = text_len ? number_of_matches : itemcount;
}

static void match(void)
{
	if (fuzzy)
	{
		fuzzymatch();
		goto done;
	}
	static char **tokv = NULL;
	static size_t tokn = 0;

	char buf[sizeof text], *s;
	size_t i, tokc = 0, len, textsize;
	struct item *item, *lprefix, *lsubstr, *prefixend, *substrend;

	strcpy(buf, text);
	/* separate input text into tokens to be matched individually */
	for (s = strtok(buf, " "); s; tokv[tokc - 1] = s, s = strtok(NULL, " "))
		if (++tokc > tokn)
		{
			tokn = tokn ? tokn * 2 : 8;
			if (!(tokv = realloc(tokv, tokn * sizeof *tokv)))
				die("cannot realloc %zu bytes:", tokn * sizeof *tokv);
		}
	len = tokc ? strlen(tokv[0]) : 0;

	matches = lprefix = lsubstr = matchend = prefixend = substrend = NULL;
	matchcount = 0;
	textsize = strlen(text) + 1;
	for (item = items; item && item->text; item++)
	{
		for (i = 0; i < tokc; i++)
			if (!fstrstr(item->text, tokv[i]))
				break;
		if (i != tokc)			/* not all tokens match */
			continue;
		matchcount++;
		/* exact matches go first, then prefixes, then substrings */
		if (!tokc || !fstrncmp(text, item->text, textsize))
			appenditem(item, &matches, &matchend);
		else if (!fstrncmp(tokv[0], item->text, len))
			appenditem(item, &lprefix, &prefixend);
		else
			appenditem(item, &lsubstr, &substrend);
	}
	if (lprefix)
	{
		if (matches)
		{
			matchend->right = lprefix;
			lprefix->left = matchend;
		}
		else
			matches = lprefix;
		matchend = prefixend;
	}
	if (lsubstr)
	{
		if (matches)
		{
			matchend->right = lsubstr;
			lsubstr->left = matchend;
		}
		else
			matches = lsubstr;
		matchend = substrend;
	}
  done:
	snprintf(numbers, sizeof numbers, "%zu/%zu", matchcount, itemcount);
	curr = sel = matches;
	calcoffsets();
}

static void insert(const char *str, ssize_t n)
{
	size_t len = strlen(text);
	if ((n > 0 && (size_t)n > sizeof text - 1 - len) || n < -(ssize_t) cursor)
		return;
	/* move existing text out of the way, insert new text, and update cursor */
	memmove(&text[(ssize_t) cursor + n], &text[cursor], len - cursor + 1);
	if (n > 0)
		memcpy(&text[cursor], str, n);
	cursor = (ssize_t) cursor + n;
	match();
}

static size_t nextrune(int inc)
{
	ssize_t n;

	/* return location of next utf8 rune in the given direction (+1 or -1) */
	for (n = (ssize_t) cursor + inc; n + inc >= 0 && (text[n] & 0xc0) == 0x80; n += inc)
		;
	return n;
}

static void movewordedge(int dir)
{
	if (dir < 0)
	{							/* move cursor to the start of the word */
		while (cursor > 0 && strchr(worddelimiters, text[nextrune(-1)]))
			cursor = nextrune(-1);
		while (cursor > 0 && !strchr(worddelimiters, text[nextrune(-1)]))
			cursor = nextrune(-1);
	}
	else
	{							/* move cursor to the end of the word */
		while (text[cursor] && strchr(worddelimiters, text[cursor]))
			cursor = nextrune(+1);
		while (text[cursor] && !strchr(worddelimiters, text[cursor]))
			cursor = nextrune(+1);
	}
}

static void keypress(XKeyEvent * ev)
{
	char buf[32];
	int len;
	size_t oldcursor;
	KeySym ksym;
	Status status;

	len = XmbLookupString(xic, ev, buf, sizeof buf, &ksym, &status);
	switch (status)
	{
	default:					/* XLookupNone, XBufferOverflow */
		return;
	case XLookupChars:
		goto insert;
	case XLookupKeySym:
	case XLookupBoth:
		break;
	}

	if (ev->state & ControlMask)
	{
		switch (ksym)
		{
		case XK_a:
			ksym = XK_Home;
			break;
		case XK_b:
			ksym = XK_Left;
			break;
		case XK_c:
			ksym = XK_Escape;
			break;
		case XK_d:
			ksym = XK_Delete;
			break;
		case XK_e:
			ksym = XK_End;
			break;
		case XK_f:
			ksym = XK_Right;
			break;
		case XK_g:
			ksym = XK_Escape;
			break;
		case XK_h:
			ksym = XK_BackSpace;
			break;
		case XK_i:
			ksym = XK_Tab;
			break;
		case XK_j:				/* fallthrough */
		case XK_J:				/* fallthrough */
		case XK_m:				/* fallthrough */
		case XK_M:
			ksym = XK_Return;
			ev->state &= ~ControlMask;
			break;
		case XK_n:
			ksym = XK_Down;
			break;
		case XK_p:
			ksym = XK_Up;
			break;

		case XK_k:				/* delete right */
			text[cursor] = '\0';
			match();
			break;
		case XK_u:				/* delete left */
			insert(NULL, -(ssize_t) cursor);
			break;
		case XK_w:				/* delete word */
			oldcursor = cursor;
			movewordedge(-1);
			len = (int)cursor - (int)oldcursor;
			cursor = oldcursor;
			insert(NULL, len);
			break;
		case XK_y:				/* paste selection */
		case XK_Y:
			XConvertSelection(dpy, (ev->state & ShiftMask) ? clip : XA_PRIMARY,
							  utf8, utf8, win, CurrentTime);
			return;
		case XK_Left:
		case XK_KP_Left:
			movewordedge(-1);
			goto draw;
		case XK_Right:
		case XK_KP_Right:
			movewordedge(+1);
			goto draw;
		case XK_Return:
		case XK_KP_Enter:
			break;
		case XK_bracketleft:
			cleanup();
			exit(1);
		default:
			return;
		}
	}
	else if (ev->state & Mod1Mask)
	{
		switch (ksym)
		{
		case XK_b:
			movewordedge(-1);
			goto draw;
		case XK_f:
			movewordedge(+1);
			goto draw;
		case XK_g:
			ksym = XK_Home;
			break;
		case XK_G:
			ksym = XK_End;
			break;
		case XK_h:
			ksym = XK_Up;
			break;
		case XK_j:
			ksym = XK_Next;
			break;
		case XK_k:
			ksym = XK_Prior;
			break;
		case XK_l:
			ksym = XK_Down;
			break;
		default:
			return;
		}
	}

	switch (ksym)
	{
	default:
	  insert:
		if (len > 0 && !iscntrl((unsigned char)buf[0]))
			insert(buf, len);
		break;
	case XK_Delete:
	case XK_KP_Delete:
		if (text[cursor] == '\0')
			return;
		cursor = nextrune(+1);
		/* fallthrough */
	case XK_BackSpace:
		if (cursor == 0)
			return;
		insert(NULL, (ssize_t) nextrune(-1) - (ssize_t) cursor);
		break;
	case XK_End:
	case XK_KP_End:
		if (text[cursor] != '\0')
		{
			cursor = strlen(text);
			break;
		}
		if (next)
		{
			/* jump to end of list and position items in reverse */
			curr = matchend;
			calcoffsets();
			curr = prev;
			calcoffsets();
			while (next && (curr = curr->right))
				calcoffsets();
		}
		sel = matchend;
		break;
	case XK_Escape:
		cleanup();
		exit(1);
	case XK_Home:
	case XK_KP_Home:
		if (sel == matches)
		{
			cursor = 0;
			break;
		}
		sel = curr = matches;
		calcoffsets();
		break;
	case XK_Left:
	case XK_KP_Left:
		if (cursor > 0 && (!sel || !sel->left || lines > 0))
		{
			cursor = nextrune(-1);
			break;
		}
		if (lines > 0)
			return;
		/* fallthrough */
	case XK_Up:
	case XK_KP_Up:
		if (sel && sel->left && (sel = sel->left)->right == curr)
		{
			curr = prev;
			calcoffsets();
		}
		break;
	case XK_Next:
	case XK_KP_Next:
		if (!next)
			return;
		sel = curr = next;
		calcoffsets();
		break;
	case XK_Prior:
	case XK_KP_Prior:
		if (!prev)
			return;
		sel = curr = prev;
		calcoffsets();
		break;
	case XK_Return:
	case XK_KP_Enter:
		puts((sel && !(ev->state & ShiftMask)) ? sel->text : text);
		fflush(stdout);
		if (!(ev->state & ControlMask))
		{
			cleanup();
			exit(0);
		}
		if (sel)
			sel->out = 1;
		break;
	case XK_Right:
	case XK_KP_Right:
		if (text[cursor] != '\0')
		{
			cursor = nextrune(+1);
			break;
		}
		if (lines > 0)
			return;
		/* fallthrough */
	case XK_Down:
	case XK_KP_Down:
		if (sel && sel->right && (sel = sel->right) == next)
		{
			curr = next;
			calcoffsets();
		}
		break;
	case XK_Tab:
		if (!sel)
			return;
		for (cursor = 0; sel->text[cursor] &&
			 cursor + (len = runelen(sel->text + cursor)) < sizeof text; cursor += len)
			;
		memcpy(text, sel->text, cursor);
		text[cursor] = '\0';
		match();
		break;
	}

  draw:
	drawmenu();
}

static void buttonpress(XEvent * e)
{
	struct item *item;
	XButtonPressedEvent *ev = &e->xbutton;
	int x = 0, y = 0, h = bh, w, i;

	if (ev->window != win)
		return;

	/* right-click: exit */
	if (ev->button == Button3)
	{
		cleanup();
		exit(1);
	}

	if (prompt && *prompt)
		x += promptw;

	/* input field */
	w = (lines > 0 || !matches) ? mw - x - numbersw : inputw;

	/* left-click on input: clear input */
	if (ev->button == Button1 && ev->x >= 0 && ev->y >= 0 && ev->y < bh &&
		ev->x < x + w + ((!lines && matches && !curr->left) ? textw("<") : 0))
	{
		text[0] = '\0';
		cursor = 0;
		match();
		drawmenu();
		return;
	}
	/* middle-mouse click: paste selection */
	if (ev->button == Button2)
	{
		XConvertSelection(dpy, (ev->state & ShiftMask) ? clip : XA_PRIMARY,
						  utf8, utf8, win, CurrentTime);
		drawmenu();
		return;
	}
	/* scroll up */
	if (ev->button == Button4 && prev)
	{
		sel = curr = prev;
		calcoffsets();
		drawmenu();
		return;
	}
	/* scroll down */
	if (ev->button == Button5 && next)
	{
		sel = curr = next;
		calcoffsets();
		drawmenu();
		return;
	}
	if (ev->button != Button1)
		return;
	if (ev->state & ~(ControlMask | LockMask | Mod2Mask))
		return;
	if (lines > 0)
	{
		/* grid: (ctrl)left-click on item */
		w = (mw - x) / columns;
		for (i = 0, item = curr; item != next; item = item->right, i++)
		{
			y = (i % lines + 1) * h;
			if (ev->x >= x + (i / (int)lines) * w && ev->x < x + (i / (int)lines + 1) * w &&
				ev->y >= y && ev->y < y + h)
			{
				puts(item->text);
				fflush(stdout);
				if (!(ev->state & ControlMask))
				{
					cleanup();
					exit(0);
				}
				sel = item;
				if (sel)
				{
					sel->out = 1;
					drawmenu();
				}
				return;
			}
		}
	}
	else if (matches)
	{
		/* left-click on left arrow */
		x += inputw;
		w = textw("<");
		if (prev && curr->left)
		{
			if (ev->x >= x && ev->x < x + w)
			{
				sel = curr = prev;
				calcoffsets();
				drawmenu();
				return;
			}
		}
		/* horizontal list: (ctrl)left-click on item */
		for (item = curr; item != next; item = item->right)
		{
			x += w;
			w = MIN(item->width, MAX(0, mw - x - textw(">") - numbersw));
			if (ev->x >= x && ev->x < x + w)
			{
				puts(item->text);
				fflush(stdout);
				if (!(ev->state & ControlMask))
				{
					cleanup();
					exit(0);
				}
				sel = item;
				if (sel)
				{
					sel->out = 1;
					drawmenu();
				}
				return;
			}
		}
		/* left-click on right arrow */
		w = textw(">");
		x = mw - w - numbersw;
		if (next && ev->x >= x && ev->x < x + w)
		{
			sel = curr = next;
			calcoffsets();
			drawmenu();
			return;
		}
	}
}

static void paste(void)
{
	char *p, *q;
	int di;
	unsigned long count, remaining;
	Atom da;

	/* we have been given the current selection, now insert it into input */
	if (XGetWindowProperty(dpy, win, utf8, 0, (sizeof text / 4) + 1, False,
						   utf8, &da, &di, &count, &remaining, (unsigned char **)&p) == Success
		&& p)
	{
		if (da == utf8 && di == 8)
		{
			count = strnlen(p, count);
			insert(p, (q = memchr(p, '\n', count)) ? q - p : (ssize_t) count);
		}
		XFree(p);
	}
	drawmenu();
}

static void readstdin(void)
{
	char *line = NULL;
	size_t i, itemsiz = 0, linesiz = 0;
	ssize_t len;

	/* read each line from stdin and add it to the item list */
	for (i = 0; (len = getline(&line, &linesiz, stdin)) != -1; i++)
	{
		if (i + 1 >= itemsiz)
		{
			if (itemsiz > SIZE_MAX / 2 / sizeof *items)
				die("too many items");
			itemsiz = itemsiz ? itemsiz * 2 : 256;
			if (!(items = realloc(items, itemsiz * sizeof(*items))))
				die("cannot realloc %zu bytes:", itemsiz * sizeof(*items));
		}
		if (line[len - 1] == '\n')
			line[len - 1] = '\0';
		if (!(items[i].text = strdup(line)))
			die("strdup:");

		items[i].out = 0;
		items[i].width = textw(line);
		inputw = MAX(inputw, items[i].width);
	}
	free(line);
	if (!feof(stdin))
		die("cannot read stdin:");
	if (items)
		items[i].text = NULL;
	itemcount = i;
	lines = MIN(lines, i);
}

static void run(void)
{
	XEvent ev;

	while (!XNextEvent(dpy, &ev))
	{
		if (XFilterEvent(&ev, win))
			continue;
		switch (ev.type)
		{
		case DestroyNotify:
			if (ev.xdestroywindow.window != win)
				break;
			cleanup();
			exit(1);
		case ButtonPress:
			buttonpress(&ev);
			break;
		case Expose:
			if (ev.xexpose.count == 0)
				drw_map(drw, win, 0, 0, mw, mh);
			break;
		case FocusIn:
			/* regrab focus from parent window */
			if (ev.xfocus.window != win)
				grabfocus();
			break;
		case KeyPress:
			keypress(&ev.xkey);
			break;
		case MappingNotify:
			XRefreshKeyboardMapping(&ev.xmapping);
			break;
		case SelectionNotify:
			if (ev.xselection.property == utf8)
				paste();
			break;
		case VisibilityNotify:
			if (ev.xvisibility.state != VisibilityUnobscured)
				XRaiseWindow(dpy, win);
			break;
		}
	}
}

static void setup(void)
{
	int x, y, i, j;
	unsigned int du;
	XSetWindowAttributes swa;
	XIM xim;
	Window w, dw, *dws;
	XWindowAttributes wa;
	XClassHint ch = { "dmenu", "dmenu" };
#ifdef XINERAMA
	XineramaScreenInfo *info;
	Window pw;
	int a, di, n, area = 0;
#endif
	/* init appearance */
	for (j = 0; j < SchemeLast; j++)
		scheme[j] = drw_scm_create(drw, colors[j], 2);

	clip = XInternAtom(dpy, "CLIPBOARD", False);
	utf8 = XInternAtom(dpy, "UTF8_STRING", False);

	/* calculate menu geometry */
	bh = drw->fonts->h + 2;
	bh = MAX(bh, (int)lineheight);
	promptw = (prompt && *prompt) ? textw(prompt) - lrpad / 4 : 0;
#ifdef XINERAMA
	i = 0;
	if (parentwin == root && (info = XineramaQueryScreens(dpy, &n)))
	{
		XGetInputFocus(dpy, &w, &di);
		if (mon >= 0 && mon < n)
			i = mon;
		else if (w != root && w != PointerRoot && w != None)
		{
			/* find top-level window containing current input focus */
			do
			{
				if (XQueryTree(dpy, (pw = w), &dw, &w, &dws, &du) && dws)
					XFree(dws);
			}
			while (w != root && w != pw);
			/* find xinerama screen with which the window intersects most */
			if (XGetWindowAttributes(dpy, pw, &wa))
				for (j = 0; j < n; j++)
					if ((a = INTERSECT(wa.x, wa.y, wa.width, wa.height, info[j])) > area)
					{
						area = a;
						i = j;
					}
		}
		/* no focused window is on screen, so use pointer location instead */
		if (mon < 0 && !area && XQueryPointer(dpy, root, &dw, &dw, &x, &y, &di, &di, &du))
			for (j = 0; j < n; j++)
				if (INTERSECT(x, y, 1, 1, info[j]) > 0)
				{
					i = j;
					break;
				}
		border_width = MIN(border_width, (unsigned int)(MIN(info[i].width, info[i].height) - 1) / 2);
		bh = MIN(bh, info[i].height - 2 * (int)border_width);
		lines = MIN(lines, (unsigned int)MAX(0, (info[i].height - 2 * (int)border_width) / bh - 1));
		mh = (lines + 1) * bh;
		if (centered)
		{
			mw = MIN(MAX((long long)inputw + promptw, min_width), info[i].width - 2 * border_width);
			x = info[i].x_org + ((info[i].width - mw) / 2) - border_width;
			y = info[i].y_org + ((info[i].height - mh) / 2) - border_width;
		}
		else
		{
			x = info[i].x_org;
			y = info[i].y_org + (topbar ? 0 : info[i].height - mh - 2 * border_width);
			mw = info[i].width - 2 * border_width;
		}

		XFree(info);
	}
	else
#endif
	{
		if (!XGetWindowAttributes(dpy, parentwin, &wa))
			die("could not get embedding window attributes: 0x%lx", parentwin);

		border_width = MIN(border_width, (unsigned int)(MIN(wa.width, wa.height) - 1) / 2);
		bh = MIN(bh, wa.height - 2 * (int)border_width);
		lines = MIN(lines, (unsigned int)MAX(0, (wa.height - 2 * (int)border_width) / bh - 1));
		mh = (lines + 1) * bh;
		if (centered)
		{
			mw = MIN(MAX((long long)inputw + promptw, min_width), wa.width - 2 * border_width);
			x = (wa.width - mw) / 2 - border_width;
			y = (wa.height - mh) / 2 - border_width;
		}
		else
		{
			x = 0;
			y = topbar ? 0 : wa.height - mh - 2 * border_width;
			mw = wa.width - 2 * border_width;
		}
	}
	snprintf(numbers, sizeof numbers, "%zu/%zu", itemcount, itemcount);
	numbersw = MIN(textw(numbers), mw);
	promptw = MIN(promptw, mw - numbersw);
	columns = MAX(1, MIN(columns, (unsigned int)(mw - promptw)));
	inputw = MIN(inputw, (mw - promptw - numbersw) / 3);
	match();

	/* create menu window */
	swa.override_redirect = True;
	swa.background_pixel = scheme[SchemeNorm][ColBg].pixel;
	swa.event_mask = ExposureMask | KeyPressMask | VisibilityChangeMask | ButtonPressMask;
	win = XCreateWindow(dpy, parentwin, x, y, mw, mh, border_width,
						CopyFromParent, CopyFromParent, CopyFromParent,
						CWOverrideRedirect | CWBackPixel | CWEventMask, &swa);
	XSetWindowBorder(dpy, win, scheme[SchemeSel][ColBg].pixel);
	XSetClassHint(dpy, win, &ch);


	/* input methods */
	if ((xim = XOpenIM(dpy, NULL, NULL, NULL)) == NULL)
		die("XOpenIM failed: could not open input device");

	xic = XCreateIC(xim, XNInputStyle, XIMPreeditNothing | XIMStatusNothing,
					XNClientWindow, win, XNFocusWindow, win, NULL);
	if (!xic)
		die("XCreateIC failed");

	XMapRaised(dpy, win);
	if (embed)
	{
		XSelectInput(dpy, parentwin, FocusChangeMask | SubstructureNotifyMask);
		if (XQueryTree(dpy, parentwin, &dw, &w, &dws, &du) && dws)
		{
			for (i = 0; (unsigned int)i < du && dws[i] != win; ++i)
				XSelectInput(dpy, dws[i], FocusChangeMask);
			XFree(dws);
		}
		grabfocus();
	}
	drw_resize(drw, mw, mh);
	drawmenu();
}

static void usage(void)
{
	fputs("usage: dmenu [-bfiv] [-l lines] [-p prompt] [-fn font] [-m monitor]\n"
		  "             [-h height]\n"
		  "             [-nb color] [-nf color] [-sb color] [-sf color]\n"
		  "             [-nhb color] [-nhf color] [-shb color] [-shf color] [-w windowid]\n",
		  stderr);
	exit(1);
}

static long long number(const char *s, long long min, long long max, int base)
{
	char *end;
	long long value;

	errno = 0;
	value = strtoll(s, &end, base);
	if (errno || !*s || *end || value < min || value > max)
		die("invalid numeric argument: %s", s);
	return value;
}

int main(int argc, char *argv[])
{
	XWindowAttributes wa;
	int i, fast = 0;

	for (i = 1; i < argc; i++)
		/* these options take no arguments */
		if (!strcmp(argv[i], "-v"))
		{						/* prints version information */
			puts("dmenu-" VERSION);
			exit(0);
		}
		else if (!strcmp(argv[i], "-b"))	/* appears at the bottom of the screen */
			topbar = 0;
		else if (!strcmp(argv[i], "-f"))	/* grabs keyboard before reading stdin */
			fast = 1;
		else if (!strcmp(argv[i], "-F"))	/* disables fuzzy matching */
			fuzzy = 0;
		else if (!strcmp(argv[i], "-c"))	/* centers dmenu on screen */
			centered = 1;
		else if (!strcmp(argv[i], "-i"))
		{						/* case-insensitive item matching */
			fstrncmp = strncasecmp;
			fstrstr = cistrstr;
		}
		else if (i + 1 == argc)
			usage();
	/* these options take one argument */
		else if (!strcmp(argv[i], "-g"))
		{						/* number of columns in grid */
			columns = number(argv[++i], 1, INT_MAX, 10);
			if (lines == 0)
				lines = 1;
		}
		else if (!strcmp(argv[i], "-l"))
		{						/* number of lines in grid */
			lines = number(argv[++i], 0, INT_MAX, 10);
			if (columns == 0)
				columns = 1;
		}
		else if (!strcmp(argv[i], "-m"))
			mon = number(argv[++i], -1, INT_MAX, 10);
		else if (!strcmp(argv[i], "-p"))	/* adds prompt to left of input field */
			prompt = argv[++i];
		else if (!strcmp(argv[i], "-fn"))	/* font or font set */
			fonts[0] = argv[++i];
		else if (!strcmp(argv[i], "-h"))
		{						/* minimum height of one menu line */
			lineheight = number(argv[++i], 0, 65535, 10);
			lineheight = MAX(lineheight, 8);
		}
		else if (!strcmp(argv[i], "-nb"))	/* normal background color */
			colors[SchemeNorm][ColBg] = argv[++i];
		else if (!strcmp(argv[i], "-nf"))	/* normal foreground color */
			colors[SchemeNorm][ColFg] = argv[++i];
		else if (!strcmp(argv[i], "-sb"))	/* selected background color */
			colors[SchemeSel][ColBg] = argv[++i];
		else if (!strcmp(argv[i], "-sf"))	/* selected foreground color */
			colors[SchemeSel][ColFg] = argv[++i];
		else if (!strcmp(argv[i], "-nhb"))	/* normal hi background color */
			colors[SchemeNormHighlight][ColBg] = argv[++i];
		else if (!strcmp(argv[i], "-nhf"))	/* normal hi foreground color */
			colors[SchemeNormHighlight][ColFg] = argv[++i];
		else if (!strcmp(argv[i], "-shb"))	/* selected hi background color */
			colors[SchemeSelHighlight][ColBg] = argv[++i];
		else if (!strcmp(argv[i], "-shf"))	/* selected hi foreground color */
			colors[SchemeSelHighlight][ColFg] = argv[++i];
		else if (!strcmp(argv[i], "-w"))	/* embedding window id */
			embed = argv[++i];
		else if (!strcmp(argv[i], "-bw"))
			border_width = number(argv[++i], 0, 65535, 10);
		else
			usage();

	if (!setlocale(LC_CTYPE, "") || !XSupportsLocale())
		fputs("warning: no locale support\n", stderr);
	if (!(dpy = XOpenDisplay(NULL)))
		die("cannot open display");
	screen = DefaultScreen(dpy);
	root = RootWindow(dpy, screen);
	if (!embed || !(parentwin = number(embed, 0, UINT32_MAX, 0)))
		parentwin = root;
	if (!XGetWindowAttributes(dpy, parentwin, &wa))
		die("could not get embedding window attributes: 0x%lx", parentwin);
	drw = drw_create(dpy, screen, root, 1, 1);
	if (!drw_fontset_create(drw, fonts, LENGTH(fonts)))
		die("no fonts could be loaded.");
	lrpad = drw->fonts->h;

#ifdef __OpenBSD__
	if (pledge("stdio rpath", NULL) == -1)
		die("pledge");
#endif

	if (fast && !isatty(0))
	{
		grabkeyboard();
		readstdin();
	}
	else
	{
		readstdin();
		grabkeyboard();
	}
	setup();
	run();

	return 1;					/* unreachable */
}
