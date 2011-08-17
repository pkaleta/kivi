#include <erl_interface.h>
#include <ei.h>
#include <stdio.h>
#include <unistd.h>

extern const char *erl_thisnodename(void);
extern short erl_thiscreation(void);

const int BUF_SIZE = 1024;

int kvconnect() {
    int sockfd;
    char *nodename = "pong@kurvinox";
    if ((sockfd = erl_connect(nodename)) < 0)
        erl_err_quit("ERROR: erl_connect failed");
    return sockfd;
}

void kvsend(int sockfd) {
    ETERM *arr[2], *ping_msg;
    arr[0] = erl_mk_pid(erl_thisnodename(), sockfd, 0, erl_thiscreation());
    arr[1] = erl_mk_atom("ping");

    ping_msg = erl_mk_tuple(arr, 2);
    unsigned char buf[BUF_SIZE];
    ErlMessage emsg;
    while (1) {
        sleep(1);
        erl_reg_send(sockfd, "pong", ping_msg);

        if (erl_receive_msg(sockfd, buf, BUF_SIZE, &emsg) == ERL_MSG) {
            printf("Ping received pong\n");
        }
    }

    erl_free_term(arr[0]);
    erl_free_term(arr[1]);
    erl_free_term(ping_msg);
}


void erl_interface_init() {
    erl_init(NULL, 0);

    int identification_number = 99;
    int creation = 1;
    char *cookie = "secret";
    if (!erl_connect_init(identification_number, cookie, creation))
        erl_err_quit("ERROR: erl_connect_init failed");
}

int main() {
    erl_interface_init();
    kvsend(kvconnect());
    return 0;
}

