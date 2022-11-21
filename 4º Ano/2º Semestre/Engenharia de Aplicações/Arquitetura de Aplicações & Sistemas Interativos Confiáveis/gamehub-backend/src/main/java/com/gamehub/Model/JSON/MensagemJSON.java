package com.gamehub.Model.JSON;

import com.fasterxml.jackson.annotation.JsonProperty;

public class MensagemJSON {
    private String conteudo;

    public MensagemJSON(@JsonProperty("conteudo") String conteudo) {
        this.conteudo = conteudo;
    }

    public String getConteudo() {
        return conteudo;
    }

    public void setConteudo(String conteudo) {
        this.conteudo = conteudo;
    }

}
