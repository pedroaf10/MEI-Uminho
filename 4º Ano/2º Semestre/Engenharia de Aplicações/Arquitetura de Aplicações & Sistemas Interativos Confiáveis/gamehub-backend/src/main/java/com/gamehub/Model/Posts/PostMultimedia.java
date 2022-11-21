package com.gamehub.Model.Posts;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.gamehub.Model.Users.Gamer;

import javax.persistence.*;
import java.time.LocalDateTime;
import java.util.List;

@Entity
public class PostMultimedia extends Post {

    @Column(columnDefinition = "TEXT")
    private String multimedia;

    @JsonIgnoreProperties({"estado", "amigos", "classificacao", "numero_classificacoes", "utilizador", "recompensas", "jogos", "caixasMensagens", "likedPosts", "dislikedPosts", "publicacoes_grupo", "publicacoes_media", "grupo"})
    @ManyToOne(fetch = FetchType.EAGER)
    @JoinColumn(name = "gamer_id")
    private Gamer gamer;

    @ManyToMany(fetch = FetchType.EAGER)
    @JoinColumn(name = "tag_id")
    private List<Tag> tags;

    public PostMultimedia(int id, String jogo, String descricao, Integer likes, LocalDateTime datetime, String multimedia, Gamer gamer, List<Tag> tags) {
        super(id, jogo, descricao, likes, datetime);
        this.multimedia = multimedia;
        this.gamer = gamer;
        this.tags = tags;
    }

    public PostMultimedia(String jogo, String descricao, Integer likes, LocalDateTime datetime, String multimedia, Gamer gamer, List<Tag> tags) {
        super(jogo, descricao, likes, datetime);
        this.multimedia = multimedia;
        this.gamer = gamer;
        this.tags = tags;
    }


    public PostMultimedia() {
        super();
    }

    public String getMultimedia() {
        return multimedia;
    }

    public void setMultimedia(String multimedia) {
        this.multimedia = multimedia;
    }

    public Gamer getGamer() {
        return gamer;
    }

    public void setGamer(Gamer gamer) {
        this.gamer = gamer;
    }

    public List<Tag> getTags() {
        return tags;
    }

    public void setTags(List<Tag> tags) {
        this.tags = tags;
    }

    @Override
    public String toString() {
        return "PostMultimedia{" +
                ", multimedia='" + multimedia + '\'' +
                ", gamer=" + gamer +
                '}';
    }
}
