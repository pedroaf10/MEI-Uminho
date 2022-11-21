package com.gamehub.Model.JSON;

import com.fasterxml.jackson.annotation.JsonProperty;

import java.util.List;

public class ListaJogosJSON {

    private List<Integer> jogos;

    public ListaJogosJSON(@JsonProperty("jogos") List<Integer> jogos) {
        this.jogos = jogos;
    }

    public List<Integer> getJogos() {
        return jogos;
    }

    public void setJogos(List<Integer> jogos) {
        this.jogos = jogos;
    }
}
