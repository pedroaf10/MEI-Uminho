package com.gamehub.Model.JSON;

import com.gamehub.Model.Users.Gamer;

public class PerfilAmigosJSON {
    Gamer amigo;
    boolean pode_classificar;

    public PerfilAmigosJSON(Gamer amigo, boolean pode_classificar) {
        this.amigo = amigo;
        this.pode_classificar = pode_classificar;
    }

    public Gamer getAmigo() {
        return amigo;
    }

    public void setAmigo(Gamer amigo) {
        this.amigo = amigo;
    }

    public boolean isPode_classificar() {
        return pode_classificar;
    }

    public void setPode_classificar(boolean pode_classificar) {
        this.pode_classificar = pode_classificar;
    }
}
