package com.gamehub.Model.JSON;

public class NaoLidasJSON {

    private int numero_mensagens_nao_lidas;
    private int id_amigo;

    public NaoLidasJSON(int numero_mensagens_nao_lidas, int id_amigo) {
        this.numero_mensagens_nao_lidas = numero_mensagens_nao_lidas;
        this.id_amigo = id_amigo;
    }

    public int getNumero_mensagens_nao_lidas() {
        return numero_mensagens_nao_lidas;
    }

    public void setNumero_mensagens_nao_lidas(int numero_mensagens_nao_lidas) {
        this.numero_mensagens_nao_lidas = numero_mensagens_nao_lidas;
    }

    public int getId_amigo() {
        return id_amigo;
    }

    public void setId_amigo(int id_amigo) {
        this.id_amigo = id_amigo;
    }
}
