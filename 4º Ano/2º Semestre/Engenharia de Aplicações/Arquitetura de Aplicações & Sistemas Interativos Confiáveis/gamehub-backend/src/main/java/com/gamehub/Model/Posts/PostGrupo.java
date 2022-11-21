package com.gamehub.Model.Posts;

import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.gamehub.Model.Users.Gamer;

import javax.persistence.*;
import java.time.LocalDateTime;

@Entity
public class PostGrupo extends Post {
    private String idioma;
    private String modoJogo;
    private int participantes;
    private String nomeEquipa;
    private String plataforma;

    @JsonIgnoreProperties({"estado", "amigos", "classificacao", "numero_classificacoes", "utilizador", "recompensas", "jogos", "caixasMensagens", "likedPosts", "dislikedPosts", "publicacoes_grupo", "publicacoes_media", "grupo"})
    @ManyToOne(fetch = FetchType.EAGER)
    @JoinColumn(name = "gamer_id")
    private Gamer gamer;

    @JsonIgnore
    @OneToOne(cascade = CascadeType.ALL, fetch = FetchType.EAGER)
    @JoinColumn(name = "grupo_id")
    private Grupo grupo;

    public PostGrupo(int id, Integer likes, LocalDateTime datetime, String jogo, String descricao, String idioma, String modoJogo, int participantes, String nomeEquipa, String plataforma, Gamer gamer, Grupo grupo) {
        super(id, jogo, descricao, likes, datetime);
        this.idioma = idioma;
        this.modoJogo = modoJogo;
        this.participantes = participantes;
        this.nomeEquipa = nomeEquipa;
        this.plataforma = plataforma;
        this.gamer = gamer;
        this.grupo = grupo;
    }

    public PostGrupo(Integer likes, LocalDateTime datetime, String jogo, String descricao, String idioma, String modoJogo, int participantes, String nomeEquipa, String plataforma, Gamer gamer, Grupo grupo) {
        super(jogo, descricao, likes, datetime);
        this.idioma = idioma;
        this.modoJogo = modoJogo;
        this.participantes = participantes;
        this.nomeEquipa = nomeEquipa;
        this.plataforma = plataforma;
        this.gamer = gamer;
        this.grupo = grupo;
    }

    public PostGrupo() {
        super();
    }


    public String getIdioma() {
        return idioma;
    }

    public void setIdioma(String idioma) {
        this.idioma = idioma;
    }

    public String getModoJogo() {
        return modoJogo;
    }

    public void setModoJogo(String modoJogo) {
        this.modoJogo = modoJogo;
    }

    public int getParticipantes() {
        return participantes;
    }

    public void setParticipantes(int participantes) {
        this.participantes = participantes;
    }

    public String getNomeEquipa() {
        return nomeEquipa;
    }

    public void setNomeEquipa(String nomeEquipa) {
        this.nomeEquipa = nomeEquipa;
    }

    public String getPlataforma() {
        return plataforma;
    }

    public void setPlataforma(String plataforma) {
        this.plataforma = plataforma;
    }

    public Gamer getGamer() {
        return gamer;
    }

    public void setGamer(Gamer gamer) {
        this.gamer = gamer;
    }

    public Grupo getGrupo() {
        return grupo;
    }

    public void setGrupo(Grupo grupo) {
        this.grupo = grupo;
    }

    @Override
    public String toString() {
        return "PostGrupo{" +
                "idioma='" + idioma + '\'' +
                ", modoJogo='" + modoJogo + '\'' +
                ", participantes=" + participantes +
                ", nomeEquipa='" + nomeEquipa + '\'' +
                ", plataforma='" + plataforma + '\'' +
                ", gamer=" + gamer +
                ", grupo=" + grupo +
                '}';
    }
}
