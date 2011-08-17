-module(pong).
-export([start/0, pong/0]).

start() ->
    io:format("Starting pong~n", []),
    register(pong, spawn(pong, pong, [])).

pong() ->
    receive
        {Pid, ping} ->
            io:format("Pong received ping from: ~s~n", [pid_to_list(Pid)]),
            Pid ! pong,
            pong();
        {Pid, stop} ->
            io:format("Pong received stop from: ~s~n", [pid_to_list(Pid)]);
        Msg ->
            io:format("Pong received strange message: ~w~n", [Msg]),
            pong()
    end.
