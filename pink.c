#include <arpa/inet.h>
#include <netinet/in.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

#define MAX_ROOMS 64
#define MAX_PLAYERS 4
#define TOKENS 4
#define TRACK_LEN 52
#define WIN_POS 57

typedef struct {
    int active, fd, color, tokens[TOKENS];
    char name[32];
} Player;

typedef struct {
    int active, turn, dice, rolled, winner;
    char code[8];
    pthread_mutex_t lock;
    Player players[MAX_PLAYERS];
} Room;

static Room rooms[MAX_ROOMS];
static pthread_mutex_t rooms_lock = PTHREAD_MUTEX_INITIALIZER;
static const int START_SQ[4] = {0, 13, 26, 39};
static const int SAFE_SQ[8] = {0, 8, 13, 21, 26, 34, 39, 47};

static uint32_t rol32(uint32_t v, int b) { return (v << b) | (v >> (32 - b)); }

static void sha1(const uint8_t *data, size_t len, uint8_t out[20]) {
    uint32_t h[5] = {0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0};
    size_t nlen = len + 1;
    while (nlen % 64 != 56) nlen++;
    uint8_t *msg = calloc(nlen + 8, 1);
    memcpy(msg, data, len);
    msg[len] = 0x80;
    uint64_t blen = (uint64_t)len * 8;
    for (int i = 0; i < 8; i++) msg[nlen + 7 - i] = (blen >> (i * 8)) & 0xFF;

    for (size_t off = 0; off < nlen + 8; off += 64) {
        uint32_t w[80];
        for (int i = 0; i < 16; i++)
            w[i] = ((uint32_t)msg[off + i * 4] << 24) | ((uint32_t)msg[off + i * 4 + 1] << 16) |
                   ((uint32_t)msg[off + i * 4 + 2] << 8) | msg[off + i * 4 + 3];
        for (int i = 16; i < 80; i++)
            w[i] = rol32(w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16], 1);
        uint32_t a = h[0], b = h[1], c = h[2], d = h[3], e = h[4];
        for (int i = 0; i < 80; i++) {
            uint32_t f = i < 20 ? ((b & c) | ((~b) & d)) : i < 40 ? (b ^ c ^ d) :
                         i < 60 ? ((b & c) | (b & d) | (c & d)) : (b ^ c ^ d);
            uint32_t k = i < 20 ? 0x5A827999 : i < 40 ? 0x6ED9EBA1 : i < 60 ? 0x8F1BBCDC : 0xCA62C1D6;
            uint32_t t = rol32(a, 5) + f + e + k + w[i];
            e = d; d = c; c = rol32(b, 30); b = a; a = t;
        }
        h[0] += a; h[1] += b; h[2] += c; h[3] += d; h[4] += e;
    }
    free(msg);
    for (int i = 0; i < 20; i++) out[i] = (h[i / 4] >> ((3 - (i % 4)) * 8)) & 0xFF;
}

static void b64_encode(const uint8_t *in, size_t len, char *out) {
    static const char t[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    size_t i = 0, j = 0;
    while (i < len) {
        uint32_t a = i < len ? in[i++] : 0, b = i < len ? in[i++] : 0, c = i < len ? in[i++] : 0;
        uint32_t v = (a << 16) | (b << 8) | c;
        out[j++] = t[(v >> 18) & 63]; out[j++] = t[(v >> 12) & 63];
        out[j++] = t[(v >> 6) & 63]; out[j++] = t[v & 63];
    }
    if (len % 3 == 1) out[j - 2] = out[j - 1] = '=';
    else if (len % 3 == 2) out[j - 1] = '=';
    out[j] = '\0';
}

static int is_safe(int gp) {
    for (int i = 0; i < 8; i++) if (SAFE_SQ[i] == gp) return 1;
    return 0;
}

static int global_pos(int c, int rel) {
    return (rel < 0 || rel > 50) ? -1 : (START_SQ[c] + rel) % TRACK_LEN;
}

static int ws_send(int fd, const char *msg) {
    size_t len = strlen(msg), hlen = 2;
    uint8_t hdr[10] = {0x81, (uint8_t)len};
    if (len > 125 && len <= 65535) {
        hdr[1] = 126; hdr[2] = (len >> 8) & 0xFF; hdr[3] = len & 0xFF; hlen = 4;
    } else if (len > 65535) {
        hdr[1] = 127; hlen = 10;
        for (int i = 0; i < 8; i++) hdr[2 + i] = (len >> ((7 - i) * 8)) & 0xFF;
    }
    return (write(fd, hdr, hlen) <= 0 || write(fd, msg, len) <= 0) ? -1 : 0;
}

static int ws_read(int fd, char *out, size_t max_len) {
    uint8_t h[2], mask[4] = {0};
    if (recv(fd, h, 2, MSG_WAITALL) <= 0 || (h[0] & 0x0F) == 0x8) return -1;
    uint64_t plen = h[1] & 0x7F;
    if (plen == 126) {
        uint8_t e[2];
        if (recv(fd, e, 2, MSG_WAITALL) <= 0) return -1;
        plen = (e[0] << 8) | e[1];
    } else if (plen == 127) {
        uint8_t e[8];
        if (recv(fd, e, 8, MSG_WAITALL) <= 0) return -1;
        plen = 0;
        for (int i = 0; i < 8; i++) plen = (plen << 8) | e[i];
    }
    if ((h[1] & 0x80) && recv(fd, mask, 4, MSG_WAITALL) <= 0) return -1;
    if (plen >= max_len) return -1;
    uint8_t *buf = malloc(plen + 1);
    if (plen > 0 && recv(fd, buf, plen, MSG_WAITALL) <= 0) { free(buf); return -1; }
    for (uint64_t i = 0; i < plen; i++) out[i] = (h[1] & 0x80) ? (buf[i] ^ mask[i % 4]) : buf[i];
    out[plen] = '\0';
    free(buf);
    return 0;
}

static void broadcast(Room *r, const char *info) {
    char json[4096];
    int pos = snprintf(json, sizeof(json),
        "{\"type\":\"state\",\"room\":\"%s\",\"turn\":%d,\"dice\":%d,\"rolled\":%d,\"winner\":%d,\"msg\":\"%s\",\"players\":[",
        r->code, r->turn, r->dice, r->rolled, r->winner, info);
    for (int i = 0, first = 1; i < MAX_PLAYERS; i++) {
        if (!r->players[i].active) continue;
        pos += snprintf(json + pos, sizeof(json) - pos,
            "%s{\"slot\":%d,\"name\":\"%s\",\"color\":%d,\"tokens\":[%d,%d,%d,%d]}",
            first ? "" : ",", i, r->players[i].name, r->players[i].color,
            r->players[i].tokens[0], r->players[i].tokens[1], r->players[i].tokens[2], r->players[i].tokens[3]);
        first = 0;
    }
    snprintf(json + pos, sizeof(json) - pos, "]}");
    for (int i = 0; i < MAX_PLAYERS; i++) if (r->players[i].active) ws_send(r->players[i].fd, json);
}

static int next_player(Room *r, int cur) {
    for (int s = 1; s <= MAX_PLAYERS; s++) {
        int idx = (cur + s) % MAX_PLAYERS;
        if (r->players[idx].active) return idx;
    }
    return cur;
}

static int can_move(Room *r, Player *p) {
    if (!r->rolled || !r->dice) return 0;
    for (int t = 0; t < TOKENS; t++) {
        int pos = p->tokens[t];
        if ((pos == -1 && r->dice == 6) || (pos >= 0 && pos + r->dice <= WIN_POS)) return 1;
    }
    return 0;
}

static void handle_move(Room *r, int slot, int tok) {
    Player *p = &r->players[slot];
    if (r->winner != -1 || r->turn != slot || !r->rolled || tok < 0 || tok >= TOKENS) return;
    int cur = p->tokens[tok], nxt = (cur == -1 && r->dice == 6) ? 0 : (cur >= 0 && cur + r->dice <= WIN_POS) ? cur + r->dice : -99;
    if (nxt == -99) return;

    p->tokens[tok] = nxt;
    char st[128];
    snprintf(st, sizeof(st), "%s hopped bunny %d ✨", p->name, tok + 1);

    int cap = 0, gp = global_pos(p->color, nxt);
    if (gp != -1 && !is_safe(gp)) {
        for (int oi = 0; oi < MAX_PLAYERS; oi++) {
            if (oi == slot || !r->players[oi].active) continue;
            Player *op = &r->players[oi];
            for (int ot = 0; ot < TOKENS; ot++) {
                if (global_pos(op->color, op->tokens[ot]) == gp) {
                    op->tokens[ot] = -1;
                    cap = 1;
                    snprintf(st, sizeof(st), "%s booped %s back home! 💕", p->name, op->name);
                }
            }
        }
    }

    int won = 1;
    for (int t = 0; t < TOKENS; t++) if (p->tokens[t] != WIN_POS) won = 0;
    if (won) {
        r->winner = p->color;
        snprintf(st, sizeof(st), "👑 %s is the Cutie Champion! 👑", p->name);
        broadcast(r, st);
        return;
    }

    int bonus = (r->dice == 6) || cap || (nxt == WIN_POS);
    r->dice = r->rolled = 0;
    if (!bonus) r->turn = next_player(r, slot);
    broadcast(r, st);
}

static void handle_roll(Room *r, int slot) {
    Player *p = &r->players[slot];
    if (r->winner != -1 || r->turn != slot || r->rolled) return;
    r->dice = (rand() % 6) + 1;
    r->rolled = 1;
    char st[128];
    if (!can_move(r, p)) {
        snprintf(st, sizeof(st), "%s rolled %d (no moves 🥺)", p->name, r->dice);
        r->dice = r->rolled = 0;
        r->turn = next_player(r, slot);
    } else {
        snprintf(st, sizeof(st), "%s rolled a %d! 🎲", p->name, r->dice);
    }
    broadcast(r, st);
}

static void serve_file(int fd, const char *path, const char *mime) {
    FILE *f = fopen(path, "rb");
    if (!f) { write(fd, "HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\n\r\n", 45); return; }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    rewind(f);
    char *body = malloc(sz);
    fread(body, 1, sz, f);
    fclose(f);
    char hdr[256];
    int hl = snprintf(hdr, sizeof(hdr), "HTTP/1.1 200 OK\r\nContent-Type: %s\r\nContent-Length: %ld\r\nConnection: close\r\n\r\n", mime, sz);
    write(fd, hdr, hl);
    write(fd, body, sz);
    free(body);
}

static void sanitize_name(char *s) {
    for (int i = 0; s[i]; i++) if (s[i] == '"' || s[i] == '\\') s[i] = '_';
}

static void *client_worker(void *arg) {
    int fd = (int)(intptr_t)arg;
    char req[4096];
    ssize_t n = recv(fd, req, sizeof(req) - 1, 0);
    if (n <= 0) { close(fd); return NULL; }
    req[n] = '\0';

    if (strncmp(req, "GET /cute.css", 13) == 0) { serve_file(fd, "cute.css", "text/css"); close(fd); return NULL; }
    if (!strstr(req, "Upgrade: websocket") && !strstr(req, "upgrade: websocket")) {
        serve_file(fd, "pink_ludo.html", "text/html"); close(fd); return NULL;
    }

    char *kh = strstr(req, "Sec-WebSocket-Key:");
    if (!kh) kh = strstr(req, "sec-websocket-key:");
    if (!kh) { close(fd); return NULL; }
    kh += 18;
    while (*kh == ' ') kh++;
    char key[128] = {0}, comb[256], b64[64], resp[512];
    for (int i = 0; kh[i] && kh[i] != '\r' && kh[i] != '\n' && i < 120; i++) key[i] = kh[i];
    snprintf(comb, sizeof(comb), "%s258EAFA5-E914-47DA-95CA-C5AB0DC85B11", key);
    uint8_t hash[20];
    sha1((uint8_t *)comb, strlen(comb), hash);
    b64_encode(hash, 20, b64);
    int rl = snprintf(resp, sizeof(resp),
        "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: %s\r\n\r\n", b64);
    write(fd, resp, rl);

    int room = -1, slot = -1;
    char msg[512];
    while (ws_read(fd, msg, sizeof(msg)) == 0) {
        char name[32] = "Cutie", code[8] = {0};
        if (strncmp(msg, "CREATE", 6) == 0) {
            if (msg[6] == ' ' && msg[7]) strncpy(name, msg + 7, 31);
            sanitize_name(name);
            pthread_mutex_lock(&rooms_lock);
            for (int i = 0; i < MAX_ROOMS; i++) {
                if (!rooms[i].active) {
                    rooms[i].active = 1;
                    snprintf(rooms[i].code, 8, "%04d", rand() % 10000);
                    rooms[i].turn = rooms[i].dice = rooms[i].rolled = 0;
                    rooms[i].winner = -1;
                    for (int p = 0; p < MAX_PLAYERS; p++) rooms[i].players[p].active = 0;
                    rooms[i].players[0] = (Player){1, fd, 0, {-1, -1, -1, -1}, ""};
                    strncpy(rooms[i].players[0].name, name, 31);
                    room = i; slot = 0;
                    break;
                }
            }
            pthread_mutex_unlock(&rooms_lock);
            if (room != -1) {
                char j[128];
                snprintf(j, sizeof(j), "{\"type\":\"joined\",\"room\":\"%s\",\"slot\":0,\"color\":0}", rooms[room].code);
                ws_send(fd, j);
                pthread_mutex_lock(&rooms[room].lock);
                broadcast(&rooms[room], "Room ready! Invite your besties 💖");
                pthread_mutex_unlock(&rooms[room].lock);
            }
        } else if (sscanf(msg, "JOIN %7s %31[^\n]", code, name) >= 1) {
            sanitize_name(name);
            pthread_mutex_lock(&rooms_lock);
            for (int i = 0; i < MAX_ROOMS; i++) {
                if (rooms[i].active && strcmp(rooms[i].code, code) == 0) {
                    for (int p = 0; p < MAX_PLAYERS; p++) {
                        if (!rooms[i].players[p].active) {
                            rooms[i].players[p] = (Player){1, fd, p, {-1, -1, -1, -1}, ""};
                            strncpy(rooms[i].players[p].name, name, 31);
                            room = i; slot = p;
                            break;
                        }
                    }
                    break;
                }
            }
            pthread_mutex_unlock(&rooms_lock);
            if (room != -1) {
                char j[128], inf[96];
                snprintf(j, sizeof(j), "{\"type\":\"joined\",\"room\":\"%s\",\"slot\":%d,\"color\":%d}", rooms[room].code, slot, slot);
                ws_send(fd, j);
                snprintf(inf, sizeof(inf), "%s hopped in! 🌸", rooms[room].players[slot].name);
                pthread_mutex_lock(&rooms[room].lock);
                broadcast(&rooms[room], inf);
                pthread_mutex_unlock(&rooms[room].lock);
            } else {
                ws_send(fd, "{\"type\":\"error\",\"msg\":\"Room not found or full 💔\"}");
            }
        } else if (room != -1 && strcmp(msg, "ROLL") == 0) {
            pthread_mutex_lock(&rooms[room].lock);
            handle_roll(&rooms[room], slot);
            pthread_mutex_unlock(&rooms[room].lock);
        } else if (room != -1 && strncmp(msg, "MOVE ", 5) == 0) {
            pthread_mutex_lock(&rooms[room].lock);
            handle_move(&rooms[room], slot, atoi(msg + 5));
            pthread_mutex_unlock(&rooms[room].lock);
        }
    }

    if (room != -1 && slot != -1) {
        pthread_mutex_lock(&rooms[room].lock);
        rooms[room].players[slot].active = 0;
        if (rooms[room].turn == slot) {
            rooms[room].rolled = rooms[room].dice = 0;
            rooms[room].turn = next_player(&rooms[room], slot);
        }
        int left = 0;
        for (int i = 0; i < MAX_PLAYERS; i++) if (rooms[room].players[i].active) left = 1;
        if (!left) rooms[room].active = 0;
        else broadcast(&rooms[room], "A cutie left the room 🌷");
        pthread_mutex_unlock(&rooms[room].lock);
    }
    close(fd);
    return NULL;
}

int main(void) {
    signal(SIGPIPE, SIG_IGN);
    srand((unsigned int)time(NULL));
    for (int i = 0; i < MAX_ROOMS; i++) pthread_mutex_init(&rooms[i].lock, NULL);

    const char *env_port = getenv("PORT");
    int port = env_port ? atoi(env_port) : 8080;

    int sfd = socket(AF_INET, SOCK_STREAM, 0), opt = 1;
    setsockopt(sfd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt));
    struct sockaddr_in addr = {.sin_family = AF_INET, .sin_addr.s_addr = INADDR_ANY, .sin_port = htons(port)};
    bind(sfd, (struct sockaddr *)&addr, sizeof(addr));
    listen(sfd, 128);
    printf("Pink Ludo running on port %d\n", port);

    while (1) {
        int cfd = accept(sfd, NULL, NULL);
        if (cfd < 0) continue;
        pthread_t tid;
        pthread_create(&tid, NULL, client_worker, (void *)(intptr_t)cfd);
        pthread_detach(tid);
    }
}