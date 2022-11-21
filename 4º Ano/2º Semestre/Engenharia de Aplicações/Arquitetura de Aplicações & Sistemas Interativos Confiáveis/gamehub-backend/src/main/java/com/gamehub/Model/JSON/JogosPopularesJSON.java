package com.gamehub.Model.JSON;

import com.gamehub.Model.Posts.Jogo;

public class JogosPopularesJSON {

    private Jogo jogo;
    private int numSeguidores;

    public JogosPopularesJSON(Jogo jogo, int numSeguidores) {
        this.jogo = jogo;
        this.numSeguidores = numSeguidores;
    }

    public Jogo getJogo() {
        return jogo;
    }

    public void setJogo(Jogo jogo) {
        this.jogo = jogo;
    }

    public int getNumSeguidores() {
        return numSeguidores;
    }

    public void setNumSeguidores(int numSeguidores) {
        this.numSeguidores = numSeguidores;
    }
}
